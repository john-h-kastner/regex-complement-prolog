regex.pdf: regex.md
	pandoc -t latex -o regex.pdf regex.md

regex.pl: regex.md
	pandoc -t plain --filter pandoc-tangle regex.md

clean:
	rm -f regex.pl regex.pdf
