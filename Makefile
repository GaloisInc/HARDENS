.PHONY: all clean

all:   README.pdf Assurance.pdf Toolchain.pdf

%.pdf: %.md
	pandoc -f markdown -t latex -o `basename $< .md`.pdf $<

clean:
	rm -f README.pdf Assurance.pdf Toolchain.pdf
