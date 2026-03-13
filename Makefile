all:
	cd priml && $(MAKE)
	echo "#!/bin/sh" > primlc
	echo "export OCAMLC=ocamlc" >> primlc
	echo "$(shell pwd)/priml/c72s \$$@" >> primlc
	chmod +x primlc

clean:
	cd priml && $(MAKE) clean
	rm -f primlc
	rm -f temp.cmi temp.cmo temp.ml a.out
