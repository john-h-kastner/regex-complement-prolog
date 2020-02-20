regex.pdf: regex.md
	pandoc -t latex -o regex.pdf regex.md

regex.pl: regex.md
	pandoc -t plain --filter pandoc-tangle regex.md

regex.html: regex.md
	pandoc -s -t html -f markdown --css=pandoc.css -o regex.html regex.md

clean:
	rm -f regex.pl regex.pdf
