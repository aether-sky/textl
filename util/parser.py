import re
import os
import shutil
import sys
import argparse
import subprocess
import xml.etree.ElementTree as xml
import uuid as UUID
import zipfile 

from string import Template

from collections import defaultdict

#==================
# Global functions
#==================

USE_LETTRINE = False
ALT_STYLE = False
SKIP_TESTS = False
PRINT_NUMBERING = False
DEBUG = True
ALL_CHS = dict()
IS_TESTING = False
EPUB_SRCDIR = "epub-src/"

def setg(s,val):
	globals()[s] = val;

def getg(s):
	return globals()[s]

def zip_folder(folder, outfile):
	with zipfile.ZipFile(outfile, 'w', zipfile.ZIP_DEFLATED) as zip_file:
		for root, _, files in os.walk(folder):
			for file in files:
				filepath = os.path.join(root, file)
				zip_file.write(filepath, os.path.relpath(filepath, start=folder))


def rmfile(fs):
	print("Moving old files: "+",".join(map(os.path.basename,fs)))
	import contextlib
	with contextlib.suppress(FileNotFoundError):
		for f in fs:
			nf = f.replace(".tex", "")
			newname = nf + "-old.tex"
			os.rename(f, newname)

def mkdirp(dir):
	os.makedirs(dir, exist_ok=True)

def readfile(name):
	with open(name, 'r') as f:
		return f.read()
	
def writefile(fname, s):
	with open(fname, 'w') as f:
		f.write(s)

def reset_globals():
	setg('USE_LETTRINE', 0)
	setg('PRINT_NUMBERING', 0)
	setg('ALT_STYLE', 0)
	setg('SKIP_TESTS', 0)
	setg('ALL_CHS', {})
	setg('IS_TESTING', False)

def debug(s):
	if DEBUG:
		print(str(s))

def warn(s):
	sys.stderr.write("WARNING: " + str(s) + "\n")

def error(s=''):
	raise Exception(s)

def expected(label,line, iswarn=False):
	s = "Expected %s, got '%s'" % (label, line)
	if iswarn:
		f = warn
	else:
		f = error
	f(s)

#====================
# AST/Representation
#====================

AST = """

(Note: endline comments are stripped before AST is produced via the following transformation: s/#.*//)

<book> := <preamble>? <chapter>+

<preamble> := <title>? <author>?

<title> := ':Tile:' [^\n]+ '\n'

<author> := ':Author:' [^\n]+ '\n'

<date> := ':Date:' [^\n]+ '\n'

<chapter> := <chsep> <chtitle> <chmatter>

<chsep> := '//!!!' [!]* '//\n'

<chtitle> := '##' <chnum> (' ' <chlabel> (' ' <chdesc>)?)? '\n'

<chnum> := [^\s]+

<chlabel> := '(' [^)\n]+ ')'

<chdesc> := [^\n]+ '\n'

<chmatter> := ( <paragraph> '\n')*

<paragraph> := ( (<dashquote> | <blocktext> | <pragma> | <br> | <text>) '\n') *

<dashquote> := [>]+ <text>

//May not contain inner <blocktext>
<blocktext> := '/' <text> '/' <attrib>?

<pragma> := '%' [\w]+

<br> := '---' | '//' ('&&&' [&]* | '---' [-]*) '//'

<text> := <textchunk>*

//NOTE: textchunk may not recurse except for plaintext, ie, ittext cannot contain ittext, dialog cannot contain dialog, and so forth
//NOTE ALSO: <esctext> falls through to <monotext> if <tag> is not found
<textchunk> := <plaintext> | <ittext> | <doubquote> | <singquote> | <sctext> | <dialog> | <esctext> | <monotext> | <inlinecomment>

//Also cannot contain /* block comments */
<plaintext> := [^\n*%{}@]+

<ittext> := '*' <text> '*'

<singquote> := '``' <text> "''"

<singquote> := '`' <text> "'"

<sctext> := '@' <text> '@'

<dialog> := '|' <text> '|' <attrib>?

<attrib> := [\w] '>'

<esctext> := '{' <tag> ' ' <text> '}'

<tag> := '%' [^\s]+

<monotext> := '{' <text> '}'

<inlinecomment> := '/*' [^*]* '*/'

"""

class MyObj:
	def __repr__(self):
		return self.__str__()

class Node(MyObj):
	def __init__(self, tag, content=None, other=None):
		self.lineno = -1
		self.chlineno = -1
		self.chunkstart = -1
		self.tag = tag
		self.content = content
		self.other = other

	def __str__(self):
		s = self.tag
		if self.content:
			s += "(%s)" % str(self.content)

		if self.other:
			s += str(self.other)
		return s

	def __repr__(self):
		s = self.tag
		s = 'Node("%s"' % self.tag
		if self.content:
			if self.tag == 'REGULAR':
				c = repr(self.content)
			else:
				c = str(self.content)

			s += ', ' + c
		s += ')'
		return s

	def __len__(self):
		if self.tag == 'REGULAR':
			return 1
		elif self.content:
			return len(self.content)
		else:
			return 0

	def __eq__(self, other):
		if self.tag != other.tag:
			return False
		if self.content != other.content:
			return False

		return self.content == other.content

	def pos(self, p):
		if self.tag in ('DIALOG','ITALICS','DOUBQUOTE','BLOCK','SINGQUOTE') and not self.content:
			error('EMPTY %s TAG at %s' % (self.tag, p))
		self.lineno = p[0]
		self.chlineno = p[1]
		self.chunkstart = p[2]
		return self

	def get_pos(self):
		return (self.lineno, self.chlineno, self.chunkstart)

	def depth(self):
		if self.tag in ('REGULAR', 'TODO', 'PRAGMA', 'BEAT_SEP'):
			return 1
		else:
			return 1 + max(map(lambda x: x.depth(), self.content))

	def merge(self, other):
		if self.tag == 'REGULAR':
			merged = self.content + ' ' + other.content
		else:
			merged = self.content + other.content
		return Node(self.tag, merged, other.other).pos(self.get_pos())

class Prelude:
	def __init__(self, author, title, date):
		self.author = author
		self.title = title
		self.date = date
	def __str__(self):
		return str(self.title) + " by " + str(self.author)

class Chapter:
	def __init__(self, title, chunks):
		self.num = title[0]
		self.label = title[1]
		self.desc = title[2]
		self.chunks = chunks
	def __str__(self):
		return "Chapter %s\n%s (%s)\n%s" % (self.num, self.label, self.desc, str(self.chunks))

class Book:
	def __init__(self, prelude, chs):
		self.prelude = prelude
		self.chs = chs
	def __str__(self):

		return str(self.prelude) + "\n" + "\n".join(map(str, self.chs))

LINE = [Node('LINE')]

def REGULAR(s): return Node("REGULAR",s)

def merge_node(a,b):
	if a.tag == b.tag and a.tag != 'PRAGMA':
		return (a.merge(b), True)
	else:
		return (a, False)

def merge_do(lst, f):
	if lst is None:
		error('(merge_do)')
	i = 0
	if len(lst) == 0:
		return lst
	elif len(lst) == 1:
		first = lst[0]
		if first.depth() > 1:
			first.content = merge_do(first.content, merge_node)
		return [first]
	while True:
		cur = lst.pop(i)
		if i < len(lst):
			next = lst.pop(i)
			(res, change) = f(cur,next)
			lst.insert(i, res)
			if not change:
				lst.insert(i+1, next)
				i += 1
			elif res.tag != 'REGULAR':
				res.content = merge_do(res.content, merge_node)
		else:
			lst.insert(i, cur)
			break
	return lst


# [Text] -> [Text]
def merge_chunks(acc):
	return merge_do(acc, merge_node)

# String -> String
def rm_comment(line):
	line = re.sub("\r", "", line)
	if len(line) > 2 and line[:2] == '##':
		return line
	line = re.sub("/\*[^*]*\*/", "", line)
	line = re.sub("(\s+)?#.*", "", line)
	return line

def isempty(line):
	return not line.strip()

def starts(line, c):
	if line != str(line):
		error('(starts)')
	return len(line) > 0 and line[0] == c

# [String] -> (Prelude, [String])
def parse_prelude(lines):
	orig = list(lines)
	title = None
	author = None
	date = None
	while lines:
		noline = lines.pop(0)
		line_text = noline[1]
		if isempty(line_text):
			continue
		if line_text[0] == '%':
			spragma = line_text[1:]
			if spragma == 'lettrine':
				setg('USE_LETTRINE', 1)
			elif spragma == 'altstyle':
				setg('ALT_STYLE', 1)
			elif spragma == 'printnum':
				setg('PRINT_NUMBERING', 1)
			elif spragma == 'skiptests':
				setg('SKIP_TESTS', 1)
			else:
				error("Unexpected global pragma '%s'" % spragma)
		if ':Title:' in line_text:
			line_text = re.sub('.*:Title:', '', line_text)
			title = line_text
		elif ':Author:' in line_text:
			line_text = re.sub('.*:Author:', '', line_text)
			author = line_text
		elif ':Date:' in line_text:
			line_text = re.sub('.*:Date:', '', line_text)
			date = line_text
		elif starts(line_text, '/'):
			lines.insert(0, noline)
			break
	if not author and not title:
		lines = orig
	return (Prelude(author, title, date), lines)

def expect(a, b):
	if a != b:
		error("Expected (%s) got (%s)" % (b,a))

def getit(s, i):
	if i < len(s):
		return s[i]

def checkfound(c, cnext, vals, last):
	for e in vals:
		if len(e) == 1 and c == e and (c != '/' or last):
			return 1
		if len(e) == 2 and cnext and c+cnext == e:
			return 2


def eat(s, ends, opens, i=0):
	#debug("EAT: %s" % (str((s, ends, opens, i))))
	accum = ''
	doDouble = False
	orig = i
	while i < len(s):
		foundend = False
		last = i == len(s) - 1
		if i <= len(s) - 3 and s[i+2] == '>' and s[i] in ['|','/']:
			foundend = True
		#print((s, (i,len(s))))
		c = s[i]
		#print("%d is last? %s-%s" % (i, last, c))
		if c == '\\':
			accum += c
			i += 1
			accum += s[i]
			i += 1
			continue
		foundend = foundend or checkfound(c, getit(s, i+1), ends, last)

		if foundend:
			#if c == '*' and i < len(s) - 1 and s[i+1] == '*':
			#	while i < len(s) and s[i] == '*':
			#		accum += s[i]
			#		i += 1
			#	continue
			if True:#else:
				if i == orig:
					return ('', i)
				i += foundend
				break
		foundstart = checkfound(c, getit(s, i+1), opens, last)
		if foundstart:
			#debug("FOUNDSTART (%s)" % s[i])
			#i += 1
			break
		accum += c
		i += 1
	return (accum, i)

def get_ctor(c):
	tag = ''
	if c == '*':
		tag = 'ITALICS'
	elif c == '/':
		tag = 'BLOCK'
	elif c == '|':
		tag = 'DIALOG'
	elif c == '{':
		tag = 'ESCAPE'
	elif c == '@':
		tag = 'SMALLCAPS'
	elif c == '`':
		tag = 'SINGQUOTE'
	elif c == '``':
		tag = 'DOUBQUOTE'
	else:
		error("Unexpected escape tag '%s'" % c)
	return lambda x: Node(tag, x)

def get_close(c):
	if c in ('*','/','@','|'):
		return c
	elif c == '{':
		return '}'
	elif c == '`':
		return "'"
	elif c == '``':
		return "''"
	else:
		error("unexpected open tag '%s'" % c)

open_tags = ['``','`','*','/','|','{','@']

def allowed_tags(lvl, cur):
	if lvl == 0:
		return list(set(open_tags) - set(cur))
	elif lvl == 1:
		return list(set(open_tags) - set(cur) - set(['/']))
	else:
		return list(set(open_tags) - set(cur) - set(['/','|']))

# String -> ([Text],Bool,Bool)
def parse_text(line, linenum, ch_linenum, charnum, i=0, lvl=0, cur=[]):
	#debug("PARSE TEXT %s" % str((line, i, cur)))
	chunks = []
	foundEnd = False
	foundTrans = False
	if line != str(line):
		error('(parse_text) %s' % line)
	if line == '---':
		return ([Node('TODO').pos((linenum,ch_linenum,i))], False, False)
	elif len(line) and line[0] == '%':
		line = line#.strip()
		line = line[1:]
		if ' ' in line:
			(left,right) = line.split(' ', 1)
		else:
			(left,right) = (line, None)
		istransclude = left == 'transclude'
		return ([Node('PRAGMA', left, right).pos((linenum,ch_linenum,i))], False, istransclude)
	elif len(line) > 1 and line[0:2] == '//':
		if line[2] == '!':
			error("Bad ch split tag: '%s'" % line)
		elif line[2] in ('-', '&'):
			return ([Node('BEAT_SEP').pos((linenum,ch_linenum,i))], False, False)
		else:
			error("Unknown separator '%s'" % line)

	while i < len(line):
		c = line[i]
		#print("C IS: " + c)
		if c == '`' and i < len(line)  - 1 and line[i+1] == '`':
			i += 1
			c = '``'
		slash_exception = i > 0 and c == '/'
		if slash_exception:
			if i+1 < len(line) - 1:
				nextc = line[i+1]
				if nextc in open_tags:
					error("impossible")
			else:
				pass#error("character '/' may not finish a tag on line %d" % linenum)
		if not slash_exception and (c in open_tags and c not in allowed_tags(lvl,cur)):
			error("tag '%s' not allowed here: %s, %d" % (c, line, linenum))
		elif c == '>' and lvl == 0:
			#print('dash')
			typ = 0
			i += 1
			if i < len(line) and line[i] == '>':
				i += 1
				typ = 1
			(_, bi) = eat(line, [], [], i)
			(parsed, end, _) = parse_text(line, linenum, ch_linenum, charnum+i, i, lvl+1, cur+['/'])
			made = Node('DASHQUOTE', parsed, typ).pos((linenum, ch_linenum, charnum))
			#print("APPEND" + str(made))
			i = bi
			chunks.append(made)

		elif c in open_tags:
			#print("open")
			end = get_close(c)
			ctor = get_ctor(c)
			(eaten, i) = eat(line, [end], [], i+1)
			(parsed, end, _) = parse_text(eaten, linenum, ch_linenum, charnum+i, 0, lvl+1, cur+[c])
			#debug("PARSED: %s" % parsed)
			made = ctor(parsed).pos((linenum, ch_linenum, charnum))
			if c in ('|','/') and i <= len(line) - 2 and line[i+1] == '>':
				made.other = line[i:i+2]
				i += 2
			chunks.append(made)
			if end:
				foundEnd = True
				break
		else:
			#print("regular")
			bi = i
			(eaten,i) = eat(line, [], open_tags, i)
			#debug("REDULAR(%s) %d -> %d" % (eaten, bi, i))
			#if i < len(line):
			#	debug("NEXTCHAR(%s)" % (repr(line[i])))
			made = REGULAR(eaten).pos((linenum,ch_linenum,charnum+bi))
			#print("REG" + str(made))
			chunks.append(made)

	return (chunks, foundEnd, False)

def is_ch_sep(line):
	if line != str(line):
		error('(is_ch_sep)')
	return re.match("//!*//", line)

def run_tests():
	global IS_TESTING
	IS_TESTING = True
	merge_tests = [
		[
			[
				Node("DIALOG", [Node("REGULAR","test dialog 1")]),
				Node("DIALOG", [Node("REGULAR","test dialog 2")]),
				Node("DIALOG", [Node("REGULAR","test dialog 3")])
			],
			[Node("DIALOG", [Node("REGULAR","test dialog 1 test dialog 2 test dialog 3")])]
		],
		[
			[
				Node("DIALOG", [Node("REGULAR","test dialog 1")]),
				Node("REGULAR","test dialog 2"),
				Node("DIALOG", [Node("REGULAR","test dialog 3")])
			]
		],
		[
			[
				Node("REGULAR","test dialog 1"),
				Node("REGULAR","test dialog 2"),
				Node("REGULAR","test dialog 3")
			],
			[
				Node("REGULAR","test dialog 1 test dialog 2 test dialog 3")
			],
		],
		[
			[
				Node("DIALOG", [
					Node("REGULAR","test dialog 1"),
					Node("REGULAR","test dialog 2"),
					Node("REGULAR","test dialog 3")
				])
			],
			[
				Node("DIALOG",[Node("REGULAR", "test dialog 1 test dialog 2 test dialog 3")])
			],
		],

	]

	for it in merge_tests:
		if len(it) == 1:
			(merged,exp) = (it[0],it[0])
		else:
			(merged,exp) = (merge_chunks(it[0]),it[1])

		if merged != exp:
			error("\n%s != \n%s" % (merged, exp))

	eat_tests = [
		#[
		#	["|I mean yeah she's kind of mean but ****|", ['*', '|'], [], 1],
		#	["I mean yeah she's kind of mean but ****", 1]
		#],
		[
			['/Name: Rift Lurker\\*/', ['*','/'], [], 1],
			['Name: Rift Lurker\\*',21]
		],
		#[
		#	['{A asterisk blank ****** test}', ['*','/','}'], [], 1],
		#	['A asterisk blank ****** test',30]
		#],

		[
			['{thing test}', ['*','}'], [], 1],
			['thing test',12]
		],
		[
			['{escaped aster\\*isk}', ['*','}'], [], 1],
			['escaped aster\\*isk',20]
		],
		[
			['/this is a block test/case with a slash in the middle/', ['/'], [], 1],
			['this is a block test/case with a slash in the middle',54]
		],
		[
			['h', ['|', '`'], [], 0],
			['h',1]
		],
		[
			["test string {inner test}", ["*"], ['{'], 0],
			['test string ', 12]
		],
		[
			["*test string {inner test}*", ["*"],[], 1],
			['test string {inner test}', 26]
		],
		[
			["|Why do you say `I' now but it was `this one' awhile ago?|I>", ["'"],[], 17],
			['I', 19]
		],
		[
			["|Why do you say `I' a|", ["|"],[], 1],
			['Why do you say `I\' a', 22]
		],
		[
			["*test string*", ["*"],[], 1],
			['test string', 13]
		],
		[
			["``test string''", ["''","'"],[], 2],
			['test string', 15]
		],
		[
			["*test string*", ["*"],[], 0],
			['', 0]
		],
		[
			["test string", ["*",'{'],[], 0],
			['test string', 11]
		]
	]

	for args,exp in eat_tests:
		res = eat(*args)
		if res[0] != exp[0]:
			error('eat fail1: "%s" != "%s"' % (res[0],exp[0]))
		if res[1] != exp[1]:
			error('eat fail2: "%s" != "%s"' % (res[1],exp[1]))

	parse_tests = [
		[
			"*What's *she* doing here? You're not really inviting *her* are you?*",
			[
				Node("ITALICS", [Node("REGULAR", "What's ")]),
				Node("REGULAR", 'she'),
				Node("ITALICS", [Node("REGULAR", " doing here? You're not really inviting ")]),
				Node("REGULAR", 'her'),
				Node("ITALICS", [Node("REGULAR", ' are you?')])
			]
		],
		[
			">dashquote example",
			[
				Node("DASHQUOTE", [Node("REGULAR", 'dashquote example')])
			]
		],
		[
			">>dashquote example2",
			[
				Node("DASHQUOTE", [Node("REGULAR", 'dashquote example2')])
			]
		],
		[
			">@dashquote example@ *example 2*",
			[
				Node("DASHQUOTE", [
					Node("SMALLCAPS", [Node("REGULAR", 'dashquote example')]),
					Node("REGULAR", ' '),
					Node("ITALICS", [Node("REGULAR", 'example 2')]),

				])
			]
		],
		[
			"|So what are we doing for reverie?|I> Igtre breaks the silence of our continued march towards our still unclear destination.",
			[
				Node("DIALOG", [Node("REGULAR", "So what are we doing for reverie?")]),
				Node("REGULAR", " Igtre breaks the silence of our continued march towards our still unclear destination.")
			]
		],
		[
			"@small@*italic*",
			[
				Node("SMALLCAPS", [Node("REGULAR", 'small')]),
				Node("ITALICS", [Node("REGULAR", 'italic')])
			]
		],
		[
			"@small@ *italic*",
			[
				Node("SMALLCAPS", [Node("REGULAR", 'small')]),
				Node("REGULAR", ' '),
				Node("ITALICS", [Node("REGULAR", 'italic')])
			]
		],
		[
			"|Test dialog,| he said, |to see how spaces work|Z>",
			[
				Node("DIALOG", [Node("REGULAR", 'Test dialog,')]),
				Node("REGULAR", ' he said, '),
				Node("DIALOG", [Node("REGULAR", 'to see how spaces work')])
			]
		],
		[
			"/Affinity: Pyromancy->Ice (high)/",
			[Node('BLOCK', [Node('REGULAR', 'Affinity: Pyromancy->Ice (high)')])]
		],
		[
			"`If she\\'s here you should---'",
			[Node('SINGQUOTE', [Node('REGULAR', "If she\\'s here you should---")])]
		],

		[
			"/Some test text/Z>",
			[Node('BLOCK', [Node('REGULAR', 'Some test text')])]
		],
		[
			"|Some test text|",
			[Node('DIALOG', [Node('REGULAR', 'Some test text')])]
		],
		[
			"|Some test `here' text|",
			[Node("DIALOG", [Node("REGULAR", 'Some test '), Node("SINGQUOTE", [Node("REGULAR", 'here')]), Node("REGULAR", ' text')])]
		],
		[
			"This is @*a more* complex@ {example of *some* text} with {nested @tag formatting@ in it} the end.",
			[
				Node("REGULAR", 'This is '),
				Node("SMALLCAPS", [
					Node("ITALICS", [Node("REGULAR", 'a more')]),
					Node("REGULAR", ' complex')
				]),
				Node("REGULAR", " "),
				Node("ESCAPE", [
					Node("REGULAR", 'example of '),
					Node("ITALICS", [Node("REGULAR", 'some')]),
					Node("REGULAR", ' text')
				]),
				Node("REGULAR", ' with '),
				Node("ESCAPE", [
					Node("REGULAR", 'nested '),
					Node("SMALLCAPS", [Node("REGULAR", 'tag formatting')]),
					Node("REGULAR", ' in it')
				]),
				Node("REGULAR", ' the end.')
			]
		],
		[
			"|Some test `h' text|",
			[Node("DIALOG", [Node("REGULAR", 'Some test '), Node("SINGQUOTE", [Node("REGULAR", 'h')]), Node("REGULAR", ' text')])]
		],
		[
			"|Asking the gods what's going to happen instead of looking at the clouds to predict the weather, or the moon to predict the tides./|",
			[]
		]

	]
	for s,exp in parse_tests:
		if exp != exp:
			error('equality fail %s' % exp)
		passed = False
		try:
			parsed = parse_text(s, 0, 0, 0)[0]
			if parsed != exp:
				pass
			else:
				passed = True
		except:
			if not exp:
				passed = True
				pass
			else:
				print("parse shouldn't fail but did %s" % s)
				raise
		if not passed:
			error('parse fail "%s"\n%s != \n%s' % (s,repr(parsed),repr(exp)))

	old_debug = getg("DEBUG")
	setg("DEBUG", False)

	italics_doc = """
//!!!//
##testch

*What's *she* doing here? You're not really inviting *her* are you?*
"""

	rendered = render_test(parse(italics_doc.split("\n")))
	if "s }" not in rendered:
		error("double italics error")

	#error()

	dialog_doc1 =  """
//!!!//
##test

|This is some test dialog which should have a close quote.|1>

Another paragraph with some, |More dialog from the same person.|1>
"""

	parsed = parse(dialog_doc1.split("\n"))
	if render_test(parsed).count("''") != 2:
		error("dialog should not be continued")

	dialog_doc2 = """
//!!!//
##test

|This is some test dialog which should have a close quote.|1>

|Another dialog same char|1> stuff
"""

	commentdoc = """
//!!!//

##test

para

Paragraph 1
Paragraph 1 more
#a comment line

Paragraph 2
"""

	parsed = parse(dialog_doc2.split("\n"))
	if render_test(parsed).count("''") != 1:
		error("dialog should be continued")

	parsed = parse(commentdoc.split("\n"))
	chunks = parsed.chs[0].chunks[0]
	if chunks[0] == []:
		error("extra empty paragraph after chapter start")
	if len(chunks) != 3:
		error("comment line incorrectly handled")
	i=0

	testdoc3 = """
//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!//

## III.A (Lorem) ipsum dolor sit amet, consectetur adipiscing elit
#o Nulla rutrum nulla neque
#o     Nullam vehicula tempus ipsum vestibulum euismod
#o     Lorem ipsum dolor sit amet, consectetur adipiscing elit
#o     In quis rhoncus ipsum
#o     Nunc malesuada et dolor efficitur euismod
#o     Maecenas a blandit eros
#o     Phasellus pretium, elit ut consectetur lobortis, urna libero tempor erat, eu luctus velit ex eu nunc
#o Nulla interdum tellus odio, tempor mollis lectus porta at
#o Ut orci velit, pretium pharetra tristique at, dignissim at magna
#o Pellentesque cursus vehicula quam a aliquet
#o Fusce cursus condimentum tellus, vitae porttitor mauris consequat vel.
Class aptent taciti sociosqu ad litora torquent per conubia nostra, per inceptos himenaeos
|Etiam a suscipit lorem, vitae varius quam.|B> Mauris sem nibh, imperdiet eget erat at, ultrices iaculis odio.
|Donec convallis tincidunt scelerisque.|A>
|Pellentesque pharetra turpis id ullamcorper pharetra.|A>
|Donec cursus at sem condimentum elementum.|B>
|Donec vitae elementum arcu.|A>
"""

	testdoc2 = """
:Author:TestAuthor's Name

:Title:Title of the story goes here

%lettrine

%printnum

%skiptests

%altstyle

//!!!//

##TEST (TITLE) DESCRIPTION OF TITLE

INCLUDE one chunks
INCLUDE two
INCLUDE three


INCLUDE more chunks

//!!!//

##TEST2 (TITLE)

/make some stuff here/Z>


//!!!//

##TEST3

/make some stuff here/

the chunks before the transclude
here

/thing/

|some dialog| he said |was another option|

%transclude TEST

the chunks
after

|some dialog| he said again |was another option|

it

"""

	testdoc = """
:Author:TestAuthor's Name

:Title:Title of the story goes here

//!!!//

##TEST (TITLE) DESCRIPTION OF TITLE

one chunks
two
three


more chunks

//!!!//

##TEST2 (TITLE) DESCRIPTION OF TITLE

%transclude TEST

//!!!//

##NUM (TITLE) DESCRIPTION OF TITLE

#single line comment

This is example line 1. #comment

This is *example* line 2.

#comment
This is *example* @line@ /*comment*/ {three}.

#comment on top
This is paragraph1 sentence1.
This is paragraph1 sentence2.
#comment between
This is paragraph1 sentence3.

/example block/
/another example block/
/yet another example block/

/alone block/

|How about some.|
he said
|Dialog for you|

|ERROR HERE.|

%skipline

---#break

This is @*a more* complex@ {%skipline example of *some* text} with {nested @tag formatting@ in it} the end.


//!!!//

##ch2 (here) stuff

|Dialog1 text here|
|some second line of dialog|
|and yet still more dialog|

|but don't merge this|

//---//

/example block/
/another example block/
/yet another example block/

|here is some dialog,| he said.
|That makes up a paragraph but then.|X>

|continues to the same paragraph|
|And is by the same speaker|X>

|continues to the same paragraph|
|And is by the same speaker|X>

|SPEAKER Y TEXT 1|
|SPEAKER Y TEXT 2|Y>

|continues to the same paragraph|
|And is by the same speaker|X>

|if you cant tell the speaker|

|dont merge them|

`sing quote'

``doub quote''

Morbi rutrum maximus ligul.

|Quisque lacinia, eros eu maximus tristique, sem nisi egestas ex, ut pellentesque .nulla ante non era.|
|Curabitur egestas lacinia felis vel pulvina.|H>

Cras sed cursus leo, nec consectetur eni.
|Etiam tempus urna dolor, ac suscipit orci bibendum scelerisqu.|B>

|Aenean tempor sed purus vel tempu.|A> Lorem ipsum dolor sit amet, consectetur adipiscing eli. Vivamus vitae cursus risus, in mattis purus.
"""

	for doc in [testdoc,testdoc2,testdoc3]:
		try:
			rendered = render_test(parse(doc.split("\n")))
			if i == 2 and 'Pellentesque' not in rendered:
				print(rendered)
				raise Exception('exception')
		except:
			error("Parse fail in test doc")
		i += 1
	setg("DEBUG", old_debug)
	reset_globals()

# =====================
## Parser
# ====================

# [String] -> ([Para], [String], Bool, Bool)
def parse_paras(lines):
	linect = 0
	beforeChunks = []
	chunks = []
	isend = False
	islast = False
	isskip = False
	chline = 0
	foundtrans = False
	while lines:
		noline = lines.pop(0)
		line_num = noline[0]
		line_text = noline[1]
		if line_text == '%skip':
			isskip = True
			while lines:
				noline = lines.pop(0)
				line_text = noline[1]
				if is_ch_sep(line_text):
					lines.insert(0, noline)
					break

			break
		if is_ch_sep(line_text):
			lines.insert(0, noline)
			isend = True
			break
		if isempty(line_text):
			linect += 1
		else:
			if linect >= 1:
				chunks.append(LINE)
			linect = 0
			lines.insert(0, noline)
			if line_text.upper() == '%STOP':
				islast = True
			else:
				(text, islast, trans) = parse_text(line_text, line_num, chline, 0)
				if trans:
					foundtrans = 1
					beforeChunks = chunks
					chunks = []
				chunks.append(text)
				lines.pop(0)
			if islast:
				break
		chline += 1
	found = 0
	transCh = None
	if foundtrans:
		i = 0
		for c in chunks:
			if len(c) == 1:
				c = c[0]
				if c.tag == 'PRAGMA':
					found = 1
					transCh = c.other
					chunks.pop(0)
					break
			i += 1
		if not found:
			error('not found')
	if transCh:
		bgrouped = group_paras(beforeChunks)
		res = []
		for c in bgrouped:
			res.append(merge_chunks(c))
		for c in ALL_CHS[transCh]:
			for k in c:
				res.append(k)
		grouped = group_paras(chunks)
		for c in grouped:
			res.append(merge_chunks(c))
		return (res, lines, isend, islast, isskip)
	else:
		grouped = group_paras(chunks)
		res = []
		for c in grouped:
			res.append(merge_chunks(c))
		return (res, lines, isend, islast, isskip)

flatten = lambda l: [item for sublist in l for item in sublist]

def group_paras(paras):
	prev = None
	allchunks = []
	cur = []
	for p in paras:
		if p[0].tag == 'LINE':
			allchunks.append(flatten(cur))
			cur = []
		else:
			cur.append(p)
	if cur:
		allchunks.append(flatten(cur))
	return allchunks


# String -> (ChNum,ChLabel,ChDesc)
def parse_title(line):
	if line != str(line):
		error('(parse_title)')
	if len(line) < 2 or line[:2] != '##':
		expected("chapter title (parse_title)", line)
	else:
		line = line[2:]
		if '(' not in line:
			return (None, line.strip(), None)
		spl = line.split("(", 1)
		num = spl[0].strip()
		spl2 = spl[1].split(')', 1)
		if len(spl2) != 2:
			return (num, spl2[0], ' ')
		return (num, spl2[0], spl2[1].strip())

def search_for_title(lines):
	for noline in lines:
		line_text = noline[1]
		if len(line_text) > 2 and line_text[0:2] == '##':
			return True



# ([String],ChNum) -> (Chapter, [String], Bool)
def parse_ch(lines,chnum):
	title = None
	islast = False
	gotsep = False
	ignoresep = False
	allpara = []
	while lines:
		if not title and not search_for_title(lines):
			warn("Found end of book. Exiting")
			return (None, lines, True)
		noline = lines.pop(0)
		line_text = noline[1]
		if not title:
			if not gotsep:
				if not starts(line_text, '/'):
					raise Exception("Expected chsep, got: '"+line_text+"'")
				else:
					ignoresep = False
					gotsep = True
			elif isempty(line_text):
				continue
			elif not starts(line_text, '#'):
				if not ignoresep:
					expected("chapter title (parse_ch)", line_text, True)
				continue
			else:
				title = parse_title(line_text)
		else:
			if chnum and title and len(title) == 3 and title[0] != chnum:
				title = None
				ignoresep = True
				continue
			lines.insert(0, noline)
			while lines:
				noline = lines.pop(0)
				if not isempty(noline[1]):
					lines.insert(0, noline)
					break
			(paras, lines, isend, islast, isskip) = parse_paras(lines)
			allpara.append(paras)
			if islast or isend or isskip:
				break
	if isskip:
		if title is not None and len(title) > 1:
			debug("Skipped chapter %s" % str(title[1]))
		return None
	if not title or not title[1]:
		return (None, lines, True)
	debug("Parsed chapter %s" % str(title[1]))
	ALL_CHS[title[0]] = allpara
	return (Chapter(title, allpara), lines, islast)


# ([String],ChNum) -> ([Chapter], [String])
def parse_chs(lines, chnum):
	chs = []
	end = False
	while lines:
		noline = lines.pop(0)
		line_text = noline[1]
		if isempty(line_text):
			continue
		lines.insert(0, noline)
		chapter = parse_ch(lines, chnum)
		if chapter:
			(ch, lines, end) = chapter
			if ch:
				chs.append(ch)
			if end:
				break

	return (chs, lines)

def is_full_comment(line):
	if line != str(line):
		error('(is_full_comment)')
	if len(line) >= 2 and line[:2] == '##':
		return False
	else:
		return len(line) >= 1 and line[0] == '#'

# [String] -> [String]
def remove_comments(lines):
	res = []
	lastcomment = False
	for noline in lines:
		lineno = noline[0]
		line_text = noline[1]
		line_text = rm_comment(line_text)
		res.append((lineno, line_text))

	res2 = []
	for noline in res:
		lineno = noline[0]
		line_text = noline[1]
		if isempty(line_text):
			lastcomment = noline
			continue
		else:
			if lastcomment:
				res2.append(lastcomment)
			lastcomment = False
			res2.append([lineno, line_text])

	return res2

def parse(lines, chnum=None):
	i = 1
	numlines = []
	for line in lines:
		numlines.append((i, line))
		i += 1
	lines = remove_comments(numlines)
	(prelude, lines) = parse_prelude(lines)
	(chs,lines) = parse_chs(lines, chnum)
	return Book(prelude, chs)

def replace_html(s):
	return s.replace("---",'—').replace("(TM)","™")

#====================
# Renderer functions
#====================
def esc_latex(s):
	s = s.replace('\\', '')
	#if s.count("'") == 1:
	#	s = s.replace("'", '`')
	return s.replace("  ", "\quad ").replace('&', "\&").replace("_", "\_").replace("%", "\%").replace("...", "\\kern0.23em.\\kern0.23em.\\kern0.23em.\\kern0.23em\\linebreak[0]").replace('+','\\texttt{+}').replace('Ms. ','Ms.\ ').replace('~', '\\textasciitilde{}')

def mk_tex_author(x):
	return "\\hfill{\\Large\\scshape{}\\let\\clearpage\\relax "+x+"}\\cleartoverso"

def mk_tex_title(x):
	if PRINT_NUMBERING:
		pre = "\\frontmatter"
	else:
		pre = "\\mainmatter"
	if ALT_STYLE:
		return pre + "\\thispagestyle{empty}\\mbox{}\\vspace{2in}\\noindent\\begin{flushright}{\\HUGE\\chapfont\\let\\clearpage\\relax " + x + "}\\\\\n\\end{flushright}\\vspace{6\\baselineskip}"
	else:
		return pre + "\\thispagestyle{empty}\\mbox{}\\vspace{2in}\\noindent\\begin{flushright}{\\HUGE\\scshape{}\\let\\clearpage\\relax " + x + "}\\\\\n\\end{flushright}\\vspace{6\\baselineskip}"

def mk_tex_chstyle(root):
	pre = """
\\newfontfamily\\altfont[ Path = %s/font/ ]{TwitterColorEmoji-SVGinOT}
\\newfontfamily\\altfonts[ Path = %s/font/, Ligatures = TeX ]{DejaVuSansMono}
""" % (root,root)

	if ALT_STYLE:
		fontstr = """
\\newfontfamily\\chapfont[ Path = %s/font/ ]{IStillKnow}
\\newfontfamily\\letterfont[ Path = %s/font/ ]{RudelsbergAlternate}
""" % (root,root)
		return """
\\makeatletter
\\def\\MT@warn@unknown{}
\\makeatother
""" + fontstr + pre + """
\\makeatletter
\\makechapterstyle{mychstyle}{
\\setlength{\\beforechapskip}{0pt}
\\renewcommand*{\\chapnamefont}{\\large\\centering}
\\renewcommand*{\\chapnumfont}{\\large}
\\renewcommand{\\chaptername}{}
%\\renewcommand*{\\printchapternum}{%
%\\chapnumfont \\ifanappendix \\thechapter \\else \\numtoName{\\c@chapter}\\fi}
%\\renewcommand*{\\printchapternum}{%
%\\chapnumfont \\ifanappendix \\thechapter \\else \\c@chapter\\fi}
\\renewcommand*{\\printchapternum}{}

\\renewcommand*{\\printchapternonum}{%\\printchapternonum
\\vphantom{\\printchaptername}%
\\vphantom{\\chapnumfont 1}%
\\afterchapternum
\\vskip -\\onelineskip}
\\renewcommand*{\\chaptitlefont}{\\Huge\\chapfont}
\\renewcommand*{\\printchaptertitle}[1]{%
\\centering\\chaptitlefont ##1\\par
}}
\\makeatother
\\chapterstyle{mychstyle}
"""
	else:
		return pre + ("""
\\newfontfamily\\letterfont[ Path = %s/font/ ]{DejaVuSansMono}
"""  % root) + """
\\newcommand{\\swelledrule}{%
\\tikz \\filldraw[scale=.015,very thin]%
(0,0) -- (100,1) -- (200,1) -- (300,0) --%
(200,-1) -- (100,-1) -- cycle;}
\\makeatletter
\\makechapterstyle{mychstyle}{%
\\setlength{\\beforechapskip}{0pt}
\\renewcommand*{\\chapnamefont}{\\large\\centering\\scshape}
\\renewcommand*{\\chapnumfont}{\\large}
\\renewcommand{\\thechapter}{\\Roman{chapter}}
\\renewcommand{\\chaptername}{}
%\\renewcommand*{\\printchapternum}{%
%\\chapnumfont \\ifanappendix \\thechapter \\else \\numtoName{\\c@chapter}\\fi}
%\\renewcommand*{\\printchapternum}{%
%\\chapnumfont \\ifanappendix \\thechapter \\else \\c@chapter\\fi}
%\\renewcommand*{\\printchapternum}{}

\\renewcommand*{\\printchapternonum}{%\\printchapternonum
\\vphantom{\\printchaptername}
\\vphantom{\\chapnumfont 1}
\\afterchapternum
\\vskip -\\onelineskip}
\\renewcommand*{\\chaptitlefont}{\\Huge\\itshape}
\\renewcommand*{\\printchaptertitle}[1]{
\\centering\\chaptitlefont ##1\\par
\\swelledrule\\vspace{0pt plus 12 pt}}}%vspace avoids overfull vbox
\\makeatother
\\chapterstyle{mychstyle}
"""

def lettrinize(s):
	spl = s.split(' ',1)
	firstword = spl[0]
	if len(spl) > 1:
		rest = spl[1]
	else:
		rest = ""
	if not re.match("[A-Z']", firstword[0]):
		return esc_latex(s)
		error("When using lettrine first char must be letter got '%s' on line %d:%d" % (text,t.lineno,chunk_num))
	else:
		restword = ''
		if len(firstword) > 1:
			restword = firstword[1:]
		return "\\lettrine{\\letterfont "+firstword[0]+"}{" + esc_latex(restword) + '}' + ' ' + rest

def render_prelude_pdf(root, texfile, texsrcdir, prelude, title_override):
	titlefile = texsrcdir+"title.tex"
	authorfile = texsrcdir+"author.tex"
	headerfile = texsrcdir+"header.tex"
	chstylefile = texsrcdir+'chstylef.tex'

	title = mk_tex_title(prelude.title or '')
	author = mk_tex_author(prelude.author or '')

	if title_override:
		title = ''
		author = ''

	rmfile((texfile,titlefile,authorfile,chstylefile))
	writefile(titlefile,title)
	writefile(authorfile,author)
	writefile(chstylefile,mk_tex_chstyle(root))
	writefile(headerfile,'')
	#print("PARSED: %s" % book)

def render_ch_pdf(ch,num_chs):
	return '\\chapter{' + ch.label + '}\n\n'

# Chunk -> String
def render_text_pdf(t, para_callback, same_speaker):
	tag = t.tag
	if tag == 'LINE':
		return '\n'
	elif tag == 'TODO':
		return '--TODO--\n\n'
	elif tag == 'REGULAR':
		ch_line_num = t.chlineno
		chunk_num = t.chunkstart
		if chunk_num == 0 and ch_line_num == 0 and USE_LETTRINE:
			text = t.content
			return lettrinize(text)
		else:
			return esc_latex(t.content)
	elif tag == 'SMALLCAPS':
		return '\\textsc{' + para_callback(t.content).lower() + '}'
	elif tag == 'ITALICS':
		return '\\emph{' + para_callback(t.content) + '}'
	elif tag == 'ESCAPE':
		return '{\\altfonts ' + para_callback(t.content) + '}'
	elif tag == 'BLOCK':
		return "\\begin{quote}\n" + para_callback(t.content) + '\n\\end{quote}'
	elif tag =='DIALOG':
		ch_line_num = t.chlineno
		chunk_num = t.chunkstart
		if chunk_num == 0 and ch_line_num == 0 and USE_LETTRINE:
			return lettrinize(t.content[0].content) + "''"
		else:
			ren = '``' + para_callback(t.content)
			if not same_speaker:
				ren += "''"
			return ren
	elif tag =='DASHQUOTE':
		pre = '' #'\\hphantom{-\\widthof{>}}>'
		return pre + para_callback(t.content)
		#return '\\quotedash{}' + para_callback(t.content)
	elif tag =='SINGQUOTE':
		return '`' + para_callback(t.content) + "'{}"
	elif tag =='DOUBQUOTE':
		return '``' + para_callback(t.content) + "''"
	elif tag == 'PRAGMA':
		if t.content == 'skipline':
			return "\\par\\bigskip\n\n"
		elif t.content == 'lit':
			return t.other
		elif t.content == 'transclude':
			if t.other not in ALL_CHS:
				error("Cannot transclude chapter %s, not found" % t.other)
			else:
				return para_callback(ALL_CHS[t.other])
		else:
			error("Unknown pragma '%s'" % t.content)
	elif tag == 'BEAT_SEP':
		return "\secbreak\n\n"
	else:
		error("Unexpected node tag '%s'" % tag)
	return str(t)

def render_ch_epub(ch, num_chs):
	if num_chs == 1:
		return ""
		#label = "*****"
	else:
		label = ch.label
	return "<div class='title'>" + label + "</div>"

def render_prelude_html(prelude):
	#@font-face {
	#	font-family: 'Cardo';
	#	src: url('E:/time/font/Cardo-regular.ttf') format('truetype');
	#}
	stylesheet = """

	body {
		background-color: #201000;
		color: #CCAA77;
		font-family: 'Arial', sans-serif;
		margin: 2em;
		padding: 0;
		text-align: justify;
	}
	h1, h2, h3, h4, h5, h6 {
		font-family: 'Arial', sans-serif;
	}

	p {
		font-family: 'Arial', sans-serif;
		text-indent: 1em;
	}

	a {
		color: #77BBBB;
		text-decoration: underline;
	}

	a:hover {
		text-decoration: underline;
	}

	a:visited {
		color: #7766BB;
	}
"""
	return f"""
	<!--DATE:{prelude.date or "NO DATE"}-->
	<!--TITLE:{prelude.title or "NO TITLE"}-->
<html>
	<head>
		<meta charset="UTF-8">
		<script type="text/javascript" src="live.js"></script>
		<style>
		{stylesheet}
		</style>
	</head>
	<body>
		<h1>{prelude.title}</h1>
		<div class="author">by {prelude.author}</div>
""" 

def render_ch_html(ch, num_chs):
	if num_chs == 1:
		label = "*****"
	else:
		label = ch.label
	return "<h3>" + label + "</h3>"

def render_text_html(t, para_callback,same_speaker):
	tag = t.tag
	if tag == 'LINE':
		return '<br/>'
	elif tag == 'TODO':
		return '--TODO--<br/><br/>'
	elif tag == 'REGULAR':
		return t.content
	elif tag == 'SMALLCAPS':
		return  '<span style="font-variant: small-caps;">' + para_callback(t.content).upper() + '</span>'
	elif tag == 'ITALICS':
		return '<i>' + para_callback(t.content) + '</i>'
	elif tag == 'ESCAPE':
		return '{ESCAPE: ' + para_callback(t.content) + '}'
	elif tag == 'BLOCK':
		return '<div style="margin-left:2em">' + para_callback(t.content) + '</div>'
	elif tag =='DIALOG':
		ren = '“' + para_callback(t.content)
		if not same_speaker:
			ren += "”"
		return ren
	elif tag =='DASHQUOTE':
		pre = 'DASHQUOTE' #'\\hphantom{-\\widthof{>}}>'
		return pre + para_callback(t.content)
		#return '\\quotedash{}' + para_callback(t.content)
	elif tag =='SINGQUOTE':
		return '‘' + para_callback(t.content) + "’"
	elif tag =='DOUBQUOTE':
		return '“' + para_callback(t.content) + "”"
	elif tag == 'PRAGMA':
		if t.content == 'skipline':
			return "<br/><br/>"
		elif t.content == 'lit':
			return ""#t.other # no latex pragmas needed
		elif t.content == 'transclude':
			if t.other not in ALL_CHS:
				error("Cannot transclude chapter %s, not found" % t.other)
			else:
				return para_callback(ALL_CHS[t.other])
		else:
			error("Unknown pragma '%s'" % t.content)
	elif tag == 'BEAT_SEP':
		return "***<br/><br/>"
	else:
		error("Unexpected node tag '%s'" % tag)
	return str(t)

def render_closing_html():
	return """
	<p>***</p>
	<p><u><a href="index.html">Back to stories</a></u></p>
	</body>
	</html>
"""

def render_prelude_txt(prelude):
	return f"""
{prelude.title}

by {prelude.author}

"""

def render_ch_txt(ch,num_chs):
	if num_chs == 1:
		return "******\n\n"
	else:
		return "******\n" + ch.label.upper() + "\n******\n\n"

def render_text_txt(t, para_callback,same_speaker):
	tag = t.tag
	if tag == 'LINE':
		return '\n'
	elif tag == 'TODO':
		return '--TODO--\n\n'
	elif tag == 'REGULAR':
		return t.content
	elif tag == 'SMALLCAPS':
		return  para_callback(t.content).upper()
	elif tag == 'ITALICS':
		return '*' + para_callback(t.content) + '*'
	elif tag == 'ESCAPE':
		return '{ESCAPE: ' + para_callback(t.content) + '}'
	elif tag == 'BLOCK':
		return "\t" + para_callback(t.content) + '\n'
	elif tag =='DIALOG':
		ren = '``' + para_callback(t.content)
		if not same_speaker:
			ren += "''"
		return ren
	elif tag =='DASHQUOTE':
		pre = 'DASHQUOTE' #'\\hphantom{-\\widthof{>}}>'
		return pre + para_callback(t.content)
		#return '\\quotedash{}' + para_callback(t.content)
	elif tag =='SINGQUOTE':
		return '`' + para_callback(t.content) + "'"
	elif tag =='DOUBQUOTE':
		return '``' + para_callback(t.content) + "''"
	elif tag == 'PRAGMA':
		if t.content == 'skipline':
			return "\n\n"
		elif t.content == 'lit':
			return t.other
		elif t.content == 'transclude':
			if t.other not in ALL_CHS:
				error("Cannot transclude chapter %s, not found" % t.other)
			else:
				return para_callback(ALL_CHS[t.other])
		else:
			error("Unknown pragma '%s'" % t.content)
	elif tag == 'BEAT_SEP':
		return "***\n\n"
	else:
		error("Unexpected node tag '%s'" % tag)
	return str(t)

class Renderer:
	def __init__(self, book, render_func, render_ch):
		self.book = book
		self.render_func = render_func
		self.render_ch = render_ch
		self.num_chs = len(book.chs)
	
	def render(self) -> str:
		return self.render_chs(self.book.chs)

	def render_chs(self, chs) -> str:
		acc = ''
		for ch in chs:
			acc += self.render_ch(ch,self.num_chs)
			prev = None
			for para in ch.chunks:
				acc += self.render_paras(para)

				prev = para
		return acc
	
	def render_paras(self, para) -> str:
		acc = ''
		i = 0
		while i < len(para):
			cur = para[i]
			dtag = self.get_dialog_tag(cur)
			same_speaker = False
			if i < len(para) - 1:
				next = para[i+1]
				dtag_next = self.get_dialog_tag(next)
				if dtag and dtag == dtag_next:
					same_speaker = True
			rendered = self.render_para(cur,same_speaker) + '\n' + '\n'
			acc += rendered
			i += 1
		return acc
	
	# [Chunk] -> String
	def render_para(self, para, same_speaker=False) -> str:
		acc = ''
		i = 0
		for t in para:
			acc += self.render_func(t,self.render_para,same_speaker and i == len(para) - 1)
			i += 1
		return acc#.strip()

	def get_dialog_tag(self, para):
		for p in para:
			if p.tag == 'DIALOG' and p.other:
				return p.other
			return
		
	
	def get_dialog_tag_end(self,para):
		if len(para) == 0:
			return None
		last = para[-1]
		return last.other

class HTMLRenderer(Renderer):
	DEPTH = 0
	def render_para(self, para, same_speaker=False) -> str:
		HTMLRenderer.DEPTH += 1
		result =  super().render_para(para, same_speaker)
		HTMLRenderer.DEPTH -= 1 
		if HTMLRenderer.DEPTH == 0:
			result = f"<p>{result}</p>"
		return result

class EpubRenderedHTML:
	def __init__(self, chs):
		self.chs = chs
class EpubRenderedCh:
	basename = "section"
	i = 3
	@staticmethod
	def get_url(k):
		return f"{EpubRenderedCh.basename}{k:04}.html"
	def __init__(self, name, content):
		self.name = name
		self.content = content
		self.index = EpubRenderedCh.i
		self.url = EpubRenderedCh.get_url(EpubRenderedCh.i)
		EpubRenderedCh.i += 1

def render_test(parsed):
	renderer = Renderer(parsed,render_text_pdf,render_ch_pdf)
	return renderer.render()

#=================
# Build functions
#=================

def build_pdf(root,proj):
	texout = "out"
	texjunk = "junk"

	texoutdir = root + "/" + texout
	texjunkdir = texoutdir + "/" + texjunk
	mkdirp(texoutdir)
	mkdirp(texjunkdir)
	command = f'xelatex -interaction=nonstopmode -halt-on-error -output-directory="{texoutdir}/" -jobname="{proj}" book.tex'
	print(command)
	process = subprocess.run(command, shell=True, capture_output=True, text=True)
	next = False
	for l in process.stdout.split("\n"):
		if "Overfull" in l or next:
			print(l)
			next = "Overfull" in l

	if process.stderr:
		print(process.stderr) 

	if process.returncode != 0:
		print(process.stdout)
		raise Exception("nonzero exit code")
	junk = [ proj + "." + ext for ext in ["aux","log"]]
	for j in junk:
		f = texoutdir + "/" + j
		d = texjunkdir + "/" + j
		#print(f"MOVE {f} -> {d}")
		shutil.move(f, d)

def write_template(fname,outname, **kwargs):
	content = readfile(fname)
	template = Template(content)
	output = template.safe_substitute(**kwargs)
	writefile(outname, output)

def write_toc_epub(rendered, include_toc_page, prelude, uuid, outdir):
	navmap = xml.Element("navMap")
	def mkPoint(root, k, url, name):
		navpoint = xml.SubElement(root, "navPoint")
		navpoint.set("class","chapter")
		navpoint.set("id", f"id{k}")
		navpoint.set("playOrder", str(k))
		navlabel = xml.SubElement(navpoint, "navLabel")
		text = xml.SubElement(navlabel, "text")
		text.text = name
		content = xml.SubElement(navpoint, "content")
		content.set("src", url)
	mkPoint(navmap, 1, EpubRenderedCh.get_url(1), "Title Page")
	if include_toc_page:
		mkPoint(navmap, 2, EpubRenderedCh.get_url(2), "Table of Contents") 
	for c in rendered.chs:
		i = c.index
		mkPoint(navmap, i, c.url, c.name)
	xml.indent(navmap)

	intocfile = EPUB_SRCDIR + "toc.ncx"
	outtocfile = outdir + "toc.ncx"
	write_template(intocfile, outtocfile, TITLE=prelude.title, AUTHOR=prelude.author,NAVMAP=xml.tostring(navmap, encoding="unicode"), UUID=uuid)

def write_manifest_epub(rendered, include_toc_page, prelude, uuid, outdir):
	manifest = xml.Element("manifest")
	def mkItem(root, k, url, typ):
		item = xml.SubElement(root, "item")
		if isinstance(k, int):
			item.set("id", f"id{k}")
		else:
			item.set("id",k)
		item.set("href", url)
		item.set("media-type", typ)
	mkItem(manifest, 1, EpubRenderedCh.get_url(1), "application/xhtml+xml")
	if include_toc_page:
		mkItem(manifest, 2, EpubRenderedCh.get_url(2), "application/xhtml+xml")
	for c in rendered.chs:
		i = c.index
		mkItem(manifest,i, c.url, "application/xhtml+xml")
	mkItem(manifest, "ncx", "toc.ncx", "application/x-dtbncx+xml")
	mkItem(manifest, "style.css", "style.css", "text/css")
	xml.indent(manifest)

	spine = xml.Element("spine")
	spine.set("toc", "ncx")
	def mkSpine(root, k):
		item = xml.SubElement(root, "itemref")
		item.set("idref", f"id{k}")
	mkSpine(spine, 1);
	if include_toc_page:
		mkSpine(spine, 2)
	for c in rendered.chs:
		i = c.index
		mkSpine(spine, i)
	xml.indent(spine)

	incontent = EPUB_SRCDIR + "content.opf"
	outcontent = outdir + "content.opf"
	write_template(incontent, outcontent, UUID=uuid,TITLE=prelude.title,MANIFEST=xml.tostring(manifest, encoding="unicode"),SPINE=xml.tostring(spine,encoding="unicode"))

def main():
	root = None
	infile = None
	chapter = None
	confdict = defaultdict(dict)

	argpars = argparse.ArgumentParser()
	argpars.add_argument("--conf")
	argpars.add_argument("--proj")
	argpars.add_argument("--format")
	argpars.add_argument("--outdir")
	args = argpars.parse_args()
	conffile = "conf"
	if args.conf:
		conffile = args.conf
	if not args.proj:
		raise Exception("Expected --proj arg")
	lines = [ line.strip() for line in open(conffile) if len(line) > 0 and line[0] != "#" and ('=' in line or '[' in line)]

	curname = 'global'
	for line in lines:
		if '[' in line:
			line = line.replace('[','').replace(']','')
			if line != 'global':
				confdict[line] = dict(confdict['global'])
			curname = line
		else:
			(lhs,rhs) = line.split("=")
			confdict[curname][lhs] = rhs
	proj = args.proj
	conf = confdict[proj]
	outformat = args.format or "txt"
	if not 'root' in conf:
		raise Exception(f"project {proj} not found (possibly invalid config)")
	root = conf['root']
	if "$" in root:
		root = root.replace('$','')
		root = os.environ[root]
	root = root + '/'
	infile = conf['input']
	chapter = conf['chapter'] if 'chapter' in conf else None

	if not SKIP_TESTS:
		run_tests()

	chnum = None

	if chapter:
		chnum = chapter

	lines = [line.strip() for line in open(infile)]

	book = parse(lines, chnum)
	if outformat == "pdf":
		texsrcdir = root + "pdf-src/"
		mkdirp(texsrcdir)
		texfile = texsrcdir+"text.tex"
		pdfrenderer = Renderer(book,render_text_pdf,render_ch_pdf)
		render_prelude_pdf(root, texfile, texsrcdir, book.prelude,chnum)
		rendered = pdfrenderer.render()
		writefile(texfile,rendered)
		build_pdf(root,proj)
		
	elif outformat == "txt":
		outfile = args.outdir+args.proj + ".txt"
		txtrenderer = Renderer(book, render_text_txt,render_ch_txt)
		prelude = render_prelude_txt(book.prelude)
		rendered = prelude + txtrenderer.render()
		writefile(outfile, rendered)
	elif outformat == "html":
		outfile = args.outdir+args.proj+".html"
		htmlrenderer = HTMLRenderer(book, render_text_html, render_ch_html)
		prelude = render_prelude_html(book.prelude)
		closing = render_closing_html()
		rendered = prelude + htmlrenderer.render() + closing
		rendered = replace_html(rendered)
		writefile(outfile, rendered)
	elif outformat == "epub":
		outdir = args.outdir + "epub-temp/"
		shutil.rmtree(outdir)
		mkdirp(outdir)

		uuid = UUID.uuid4()
		htmlrenderer = HTMLRenderer(book, render_text_html, render_ch_epub)
		numchs = len(htmlrenderer.book.chs)
		include_toc_page = numchs > 1
		chapters = []
		for c in htmlrenderer.book.chs:
			ch = htmlrenderer.render_ch(c, htmlrenderer.num_chs)
			chname = c.label
			for para in c.chunks:
				ch += htmlrenderer.render_paras(para)
			chapter = EpubRenderedCh(chname, ch)
			chapters.append(chapter)
		rendered = EpubRenderedHTML(chapters)
		
		write_toc_epub(rendered, include_toc_page, book.prelude, uuid, outdir)
		write_manifest_epub(rendered, include_toc_page, book.prelude, uuid, outdir)
		
		cwd = os.getcwd()
		meta_inf_from = cwd + "/" + EPUB_SRCDIR + "/META-INF"
		meta_inf_to = outdir +"/META-INF"
		shutil.copytree(meta_inf_from, meta_inf_to, dirs_exist_ok=True)

		cssname = "style.css"
		incss = cwd + "/" + EPUB_SRCDIR + "/" + cssname
		outcss = outdir + "/" + cssname
		shutil.copy2(incss, outcss)

		intitle = EPUB_SRCDIR + "/" + "title_template.html"
		outtitle = outdir + "/" + EpubRenderedCh.get_url(1)
		write_template(intitle, outtitle, TITLE=book.prelude.title, AUTHOR=book.prelude.author)

		intoc = EPUB_SRCDIR + "/" + "toc_template.html"
		outtoc = outdir + "/" + EpubRenderedCh.get_url(2)
		toccontent = ""
		toccontent += f"<p style='margin:0'><a href='{EpubRenderedCh.get_url(1)}'>Title Page</a></p>\n"
		toccontent += f"<p style='margin:0'><a href='{EpubRenderedCh.get_url(2)}'>Table of Contents</a></p>\n"
		for c in rendered.chs:
			toccontent += f"<p style='margin:0'><a href='{c.url}'>{c.name}</a></p>\n"
		write_template(intoc, outtoc, CONTENT=toccontent)

		
		for c in rendered.chs:
			url = c.url
			outname = outdir + "/" + url
			print(f"writing {url} to {outname}")
			write_template(EPUB_SRCDIR + "/" + "ch_template.html", outname, CONTENT= c.content)

		outzip = args.outdir + "/" + proj
		zip_folder(outdir, outzip + ".zip")
		os.rename(outzip + '.zip', outzip + '.epub')
			
	else:
		raise Exception(f"format '{outformat}' not implemented")




if __name__ == '__main__':
	main()
