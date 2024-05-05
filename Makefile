all: build/index.html

regex.pl: regex.md
	pandoc -t plain --filter pandoc-tangle regex.md

build/index.html: regex.md build/
	pandoc -s -t html -f markdown --css='/pandoc.css' -o build/index.html regex.md

build/:
	mkdir -p build

clean:
	rm -rf build
