import os
import sys
import time
import subprocess
import datetime


def timefunc(f):
	def inner(*args, **kwargs):
		start = time.time()
		res = f(*args, **kwargs)

		print("Time taken: %.03fs" % (time.time() - start))
		return res
	return inner

def get_time(f):
	return os.stat(f).st_mtime


class RunException(Exception):
	def __init__(self, out, err):
		self.out = out
		self.err = err
		super(RunException, self).__init__()

@timefunc
def build(name):
	outp = run("./util/build %s html" % name)
	errs = [p for p in outp if len(p) > 0 and p[0] == "!" ]
	if errs:
		for p in outp:
			print(p)

	print("Build complete", end="")
	if errs:
		print(" with %d errors" % len(errs), end="")
	print()

def count(root, f, docount):
	if docount:
		lines = run('python3 "%s/util/new_count.py" d "%s" s "f%s"' % (root,root,f))
		for l in lines:
			print(l)

def run_build(root, filename, name, docount):
	print("Running build at " + datetime.datetime.now().strftime("%H:%M:%S %Y-%m-%d "))
	count(root,filename, docount)
	try:
		build(name)
	except RunException as exc:
		for line in exc.out:
			print(line)
		for line in exc.err:
			print(line)

def run(args, errok=False):
	#print(args)
	p = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
	out, err = p.communicate()
	err = err.decode("utf-8")
	out = out.decode("utf-8")
	haserror = p.returncode != 0 or err
	if haserror and not errok:
		print(err.rstrip().split("\n"))
		raise RunException(out.rstrip().split("\n"), err.rstrip().split("\n"))
	out = out.rstrip().split("\n")
	return out

def get_arg(pos):
	if len(sys.argv) <= pos:
		return ""
	else:
		return sys.argv[pos]

def main():
	root = get_arg(1) + '/'
	filename = get_arg(2)
	name = get_arg(3)
	startbuild = "b" in sys.argv
	docount = "c" in sys.argv

	print(f"CONF: {root} {filename} {name}")
	if not filename or not name:
		print("Using default")
		root = os.environ["STORY_ROOT"]
		filename = "text.text"
		name = "spider"

	if startbuild:
		run_build(root,filename, name, docount)
	t1 = get_time(filename)
	while True:
		time.sleep(1)
		t2 = get_time(filename)
		if t1 != t2:
			run_build(root,filename, name, docount)
		t1 = t2

if __name__ == '__main__':
	main()

