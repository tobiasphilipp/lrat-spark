external_tools:
	make -C cake_lpr
	make -C drat-trim

build:
	gprbuild -Pchecker -p -we -Xver=debug
	gprbuild -Pchecker -p -we -Xver=release
	strip --strip-all bin/release/checker

clean:
	gprclean -Pchecker
	rm -rf obj
	rm -rf bin

proof:
	gnatprove -Pchecker -Xver=debug  -j4 --level=4 --timeout=120

.PHONY: external_tools build clean proof
