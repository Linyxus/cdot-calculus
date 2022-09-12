FROM coqorg/coq:8.13-ocaml-4.13-flambda
RUN opam install -j4 coq-tlc
WORKDIR /projects
