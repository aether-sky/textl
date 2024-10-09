import sys
import shutil
import re
import os

OUT_DIR = f"{os.environ['STORY_ROOT']}/out/"
PUBLISH_DIR = f"{os.environ['STORY_ROOT']}/stories-published/"
AUTHOR_OVERRIDE = "Sky"

def main():
	names = sys.argv[1:]
	print("Publishing: " + ", ".join(names))
	for n in names:
		move_from = OUT_DIR + n + ".html"
		move_to  = PUBLISH_DIR + n + ".html"
		
		shutil.copy(move_from, move_to)
		if AUTHOR_OVERRIDE:
			contents = open(move_to, "r").read()
			replaced = re.sub('(<div class="author">by )(.+)(</div>)', fr'\1{AUTHOR_OVERRIDE}&nbsp;\3', contents) #nbsp in case the author's name already matches
			if contents == replaced:
				print(f"WARNING: author replace failed for {move_to}")
			open(move_to, "w").write(replaced)


if __name__ == '__main__':
	main()