docs = README.html

.PHONY: build

build:
	lake build

.PHONY: clean

clean:
	rm -f $(docs)

.PHONY: doc

doc: $(docs)

$(docs): %.html: %.md
	pandoc -f markdown_strict -t html5 -s -o $@ $^
