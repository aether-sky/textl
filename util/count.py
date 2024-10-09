
import git
import re
import sqlite3
import argparse
import glob
import os

from typing import Any
from datetime import datetime
from collections import defaultdict, namedtuple

WORDS_PER_LINE = 11
USE_CACHE = True
DEBUG = False 
DEBUG_CACHE = True
DB_NAME = 'count_cache.db'

def debug(*s):
	if DEBUG:
		s = ' '.join(map(str,list(s)))
		print(f"DEBUG:{s}")


def debug_cache(*s):
	if DEBUG_CACHE:
		debug(*s)

def find_file(name):
	pattern = f'**/{name}.text'
	result = glob.glob(pattern, recursive=True)

	if len(result) == 1:
		return result[0]

	else:
		raise Exception(f"couldn't find match for {name}")


def slurp_commit(blob):
	return blob.data_stream.read().decode('utf-8')

def is_sec_break(line):
	if len(line) < 5:
		return

	if line[:5] in ["//!!!", "//&&&", "//---"]:
		return line[2:5]

def filter_line(line):
	if is_sec_break(line) or (len(line) > 3 and line[:4] == "---#"):
		line = ""
	line = re.sub("^#.*", "", line)
	line = re.sub("\|\w>", "", line)
	line = re.sub("#.*", "", line)
	line = re.sub("^--.*", "", line)
	line = re.sub("[|@#$>]", "", line)
	line = re.sub("/\*[^\*]*\*/", "", line)
	line = re.sub("_+", "", line)
	line = re.sub("[ ]+", " ", line)
	line = re.sub("(^ )|( $)", "", line)
	return line

def count_lines(lines):
	ct = 0
	replaced = []
	for line in lines:
		#print(line)
		line = re.sub("#.*", "", line)
		line = re.sub("/\*[^\*]*\*/", "", line)
		line = re.sub("<[^>]+>", "", line)
		line = re.sub("\w>", "", line)
		ls = re.split("([.?!\|]|---|``| - )",line)
		ls = list(map(lambda x: x.strip(), ls))
		for l in ls:
			if len(l) > 1:
				replaced.append(l)
		#replaced += ls
		#replaced.append(line)
		line = filter_line(line)
		if line:
			ct += line.count(' ') + 1
	result = (replaced, ct)
	#prevfile = (numlines,hs, result)
	return result

def diff_lines(prevlines, lines2, prevd=None):
	if not prevd:
		prevd = defaultdict(int)
		for line in prevlines:
			line = strip_formatting(line)
			if line:
				prevd[line] += 1

	d2 = defaultdict(int)
	for line in lines2:
		line = strip_formatting(line)
		if line:
			d2[line] += 1

	diff = 0

	for line,ct in prevd.items():
		if line not in d2:
			diff += ct
			#print(f"EDITED {line}")

	return (diff, d2)

def mkpairs(ls):
	return list(zip(ls, ls[1:]))

def strip_formatting(line):
	line = filter_line(line)
	line = re.sub("\r", "", line)
	line = re.sub("\n", "", line)
	line = re.sub("\w>", "", line)
	line = re.sub("#.*", "", line)
	line = re.sub("_+", "", line)
	line = re.sub("/\*[^*]*\*\/", "", line)
	line = re.sub("\s+$", "", line)
	line = re.sub("``", "", line)
	line = re.sub("`", "", line)
	line = re.sub("/", "", line)
	line = re.sub("''", "", line)
	line = re.sub("'", "", line)
	line = line.strip()

	return line

def get_rename(repo, file):
	for commit in repo.iter_commits(paths=file):
		diffs = commit.diff(commit.parents or None)
		for diff in diffs:
			if diff.renamed and diff.a_path == file:
				return diff.rename_to
	return None

def get_renames(repo, file):
	renames = [file]
	while True:
		rename = get_rename(repo,file)
		file = rename
		if file:
			renames.insert(0,file)
		else:
			break
	return renames

def setup_db(nuke):
	if USE_CACHE:
		db = sqlite3.connect(DB_NAME)
		cursor = db.cursor()
		
		if nuke:
			debug_cache("Clearing out db tables...")
			cursor.execute("DROP TABLE IF EXISTS counts")
			cursor.execute("DROP TABLE IF EXISTS renames")
			cursor.execute("DROP TABLE IF EXISTS last")
			db.commit()

		debug_cache("Creating db tables...")
		cursor.execute("""
			CREATE TABLE IF NOT EXISTS counts (
				file TEXT,
				added INTEGER,
				edited INTEGER,
				date DATE,
				PRIMARY KEY (file, date)
			)
		""")
		
		cursor.execute("""
			CREATE TABLE IF NOT EXISTS renames (
				orig TEXT PRIMARY KEY,
				prev TEXT
			)
		""")

		cursor.execute("""
			CREATE TABLE IF NOT EXISTS last (
				id INTEGER PRIMARY KEY,
				name TEXT
			)
		""")


		return (db,cursor)
	else:
		debug_cache("No setup to do, caching is disabled")
		return (None,None)

def get_last_name(cache, name):
	if USE_CACHE:
		fetched = cache.execute("""
			SELECT name
			FROM last
			WHERE id = 1
		""").fetchall()
		if fetched and fetched[0]:
			return fetched[0][0]
	else:
		return name

def put_last_name(cache, name):
	if USE_CACHE:
		cache.execute("""
			INSERT INTO last (id, name) 
			VALUES (?, ?)
			ON CONFLICT(id) 
			DO UPDATE SET name=excluded.name
		""", (1, name))

def get_cached_renames(cache, file):
	if USE_CACHE:
		fetched = cache.execute("""
			select prev
			from renames
			where orig = ?
		""", (file,)).fetchall()
		if fetched:
			renames = fetched[0][0]
			debug_cache(f"Got cached renames: {renames}")
			renames = re.split(",", renames) if renames else None
			return renames
		else:
			debug_cache("Didn't find cached renames")


	return None

def put_cached_renames(cache, file, renames):
	if USE_CACHE:
		debug_cache(f"Storing renames for {file}: {renames}")
		renames_str = ",".join(renames)
		cache.execute("""
			INSERT OR IGNORE INTO renames (orig, prev) 
			VALUES (?, ?)
			""", (file,renames_str))


def get_cached_count(cache, file, date):
	if USE_CACHE:
		res = cache.execute("""
			select added, edited
			from counts
			where date = ? and file = ?
		""", (date, file)).fetchall()
		res = res[0] if res and len(res)>0 else None
		debug_cache(f"Pulling cached count for {file},{date}: {res}")
		return res
	else:
		return None
	


def put_cached_count(cache, file, date, num_added, num_edited_raw):
	if USE_CACHE:
		debug_cache(f"Inserting into cache {file},{date}: {num_added}, {num_edited_raw}")
		cache.execute("""
				INSERT OR IGNORE INTO counts (file, date, added, edited) 
				VALUES (?, ?, ?, ?)
		""", (file,date,num_added,num_edited_raw))

def close_db(db):
	if USE_CACHE:
		debug_cache("Closing db...")
		db.commit()
		db.close()


Entry = namedtuple("Entry", ["lines","count","date","filename","isdirty"])

def split_lines(s):
	return s.splitlines()

def count_file(f):
	date = datetime.now()
	contents = open(f, 'r').read()
	lines = split_lines(contents)
	(replaced, ct) = count_lines(lines)
	return Entry(replaced, ct, date, f, True)

def print_cols(lst):
	widths = [max(len(str(x)) for x in col) for col in zip(*lst) ]
	for data in lst:
		print("  ".join(f"{str(item):>{width}}" for item, width in zip(data, widths)))

def resolve_name(cache : Any, name : str) -> str:
	if not name:
		name = get_last_name(cache, name)
	if not name:
		raise Exception("Name to track needed and none found in cache or cache disabled.")
	put_last_name(cache,name)
	if ".text" not in name:
		name = find_file(name)
	return name

def run_count(cache, name):
	repo = git.Repo(os.environ["STORY_ROOT"])
	name = resolve_name(cache, name)
	all_names = get_cached_renames(cache, name)
	if not all_names:
		all_names = get_renames(repo,name)
		put_cached_renames(cache, name, all_names)
	print(f'Tracking {", ".join(all_names)}')
	commits = list(repo.iter_commits(paths=all_names))
	revs = []
	for commit in reversed(commits):
		date = commit.committed_datetime
		blob = None
		for f in reversed(all_names):
			try:
				blob = commit.tree / f
				break
			except KeyError:
				pass
		if not blob:
			debug(f"WARNING: Couldn't find {f} among {all_names} at {date}")
			continue
		revs.append((date, slurp_commit(blob), f))

	counted = []
	for r in revs:
		date = r[0]
		contents = r[1]
		file = r[2]
		lines = split_lines(contents)
		(ls,ct) = count_lines(lines)
		entry = Entry(ls,ct,date,file,False)
		counted.append(entry)
		debug(entry.date,entry.count)
	counted.append(count_file(file))
	zipped = mkpairs(counted)
	zipped.insert(0,(None,counted[0]))
	prevd = None
	data = []
	for (a,b) in zipped:
		date = b.date
		file = b.filename
		cached = get_cached_count(cache, file, date) if not b.isdirty else None
		if cached:
			(count,diff) = cached
		else:
			if a is not None:
				(diff,d) = diff_lines(a.lines, b.lines, prevd)
				prevd = d
				count = b.count - a.count
			else:
				(diff,d) = (0,None)
				count = b.count
			if not cached and not b.isdirty:
				put_cached_count(cache, file, date, count, diff)

		date = b.date.strftime('%Y-%m-%d')
		if count == 0 and b.isdirty:
			debug("No difference in current rev. Skipping line.")
			continue
		data.append((date, b.count, f"{count} words added", f"{diff} lines edited"))
		#print(f"{date} {b.count}, {count} words added, {diff} lines edited")
	print_cols(data)

def count_all():
	filter_list = [
		"isekai_notes_outline.text",
		"(tiny_ideas).text",
		"tower_short.text"
	]
	nomatch = [
		"draft",
		"ideas_",
		"nonstories/",
		"learning/" 
	]
	pattern = '**/*.text'
	files = glob.glob(pattern, recursive=True)
	count = 0
	lst = []
	maxlen = 0
	for fname in files:
		if any(map(lambda m: m in fname,nomatch)):
			continue
		if fname in filter_list:
			continue
		lines = split_lines(open(fname,"r").read())
		(_,ct) = count_lines(lines)
		name = fname.split("/")[-1].split(".")[0]
		lst.append((fname,ct))
		maxlen = max(len(fname),maxlen)
		count += ct
	lst.append(("total", count))
	lst = sorted(lst, key=lambda x: x[1])
	for l in lst:
		name = l[0]
		ct = l[1]
		print(f'{name:<{maxlen+1}}{ct}')


def get_args():
	global USE_CACHE
	argpars = argparse.ArgumentParser()
	argpars.add_argument("file_to_track",default="dummy",nargs='?')
	argpars.add_argument("--nuke",action='store_true')
	argpars.add_argument("--no-cache",action='store_true')
	argpars.add_argument("--all-count",action='store_true')
	args = argpars.parse_args()
	if args.no_cache:
		USE_CACHE = False
	if args.file_to_track == "dummy":
		args.file_to_track = None
	if args.nuke and not USE_CACHE:
		print("WARNING: Option --nuke ignored because cache is disabled")
	debug(args)
	return args

def main():
	args = get_args()
	if args.all_count:
		count_all()
		return
	(db, cache) = setup_db(args.nuke)
	try:
		run_count(cache, args.file_to_track)
	finally:
		close_db(db)

if __name__ == '__main__':
	main()

