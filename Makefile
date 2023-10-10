SRCFILES = src/*.ml src/*.mli

OCAMLFORMAT = ocamlformat \
	--inplace \
	$(SRCFILES)

OCPINDENT = ocp-indent \
	--inplace \
	$(SRCFILES)

.PHONY: all
all:
	./update-version-string.sh
	dune build @all

.PHONY: release-static
release-static :
	./update-version-string.sh
	OCAMLPARAM='_,ccopt=-static' dune build --release src/tamgram.exe
	OCAMLPARAM='_,ccopt=-static' dune build --release src/tamgram_rewrite_dot.exe
	mkdir -p statically-linked
	cp -f _build/default/src/tamgram.exe statically-linked/tamgram
	cp -f _build/default/src/tamgram_rewrite_dot.exe statically-linked/tamgram-rewrite-dot

.PHONY: debug-draft
debug-draft:
	dune exec src/tamgram.exe -- debug-tg draft.tg - # --stop-before-stage 20

.PHONY: compile-draft
compile-draft:
	dune exec src/tamgram.exe -- compile draft.tg . -f

.PHONY: debug-test
debug-test:
	dune exec src/tamgram.exe -- debug-tg test.tg - --name --stop-before-stage 25

.PHONY: compile-examples
compile-examples:
	cd examples/EMVerify && make
	./compile-examples.sh dev

.PHONY: compile-examples-all
compile-examples-all:
	./compile-examples.sh dev all-styles

# .PHONY: compile-examples
# compile-examples:
# 	./compile-examples.sh

.PHONY: compile-test
compile-test:
	dune exec src/tamgram.exe -- compile test.tg . -f

.PHONY: compile-tute
compile-tute:
	dune exec src/tamgram.exe -- compile examples/Tutorial.tg examples/Tutorial.tg.spthy -f

.PHONY: debug-wpa2
debug-wpa2:
	dune exec src/tamgram.exe -- debug-tg wpa2-tg/wpa2_four_way_handshake.tg - # --stop-before-stage 21

.PHONY: compile-wpa2
compile-wpa2:
	dune exec src/tamgram.exe -- compile wpa2-tg/wpa2_four_way_handshake.tg wpa2-tg/wpa2_four_way_handshake.spthy -f

.PHONY: manual-html
manual-html:
	mdbook build doc/

.PHONY: manual-pdf
manual-pdf:
	rm -f manual.pdf
	podman run --rm -v "$$(pwd):/data" --user root:root docker.io/pandoc/latex doc/*.md \
		--from markdown+auto_identifiers+tex_math_dollars \
		--toc \
		-o manual.pdf

.PHONY: format
format :
	$(OCPINDENT)

.PHONY: benchmark
benchmark:
	./benchmark.sh

.PHONY: clean-benchmark
clean-benchmark:
	rm -r bench_*/

.PHONY : clean
clean:
	dune clean
