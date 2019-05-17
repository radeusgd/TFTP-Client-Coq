all: extract
				ocamlbuild main.byte

extract: extraction.v TFTP_Core.vo
				coqtop -batch -load-vernac-source $<

%.vo: %.v
				coqc $<

clean:
				rm -f *.o *.cmi *.cmo *.cmx *.vo
