SUPPRESS_NTR = field_types field_type field_assns field_assn type_binding term_binding varset N
OTT_FILES = grammar.ott rules.ott
OTT_OPTS = -tex_show_meta false -tex_wrap false -picky_multiple_parses false $(SUPPRESS_NTR:%=-tex_suppress_ntr %)
OTT_TEX = ott.tex

BIB = rae
PAPER = layout-poly

all: $(PAPER).pdf

clean:
	rm -f *.aux *.bbl *.ptb *.pdf *.toc *.out *.run.xml
	rm -f *.log *.bcf *.fdb_latexmk *.fls *.blg
	rm -f $(OTT_TEX)
	rm -f $(PAPER).pdf $(PAPER).tex

$(OTT_TEX): $(OTT_FILES)
	ott $(OTT_OPTS) -o $@ $^

%.tex: %.lhs ocaml.fmt
	lhs2TeX -o $@ $^

%.pdf: %.tex $(OTT_TEX) $(BIB).bib
	latexmk -pdf $*
