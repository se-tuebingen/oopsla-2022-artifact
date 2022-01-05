# syntax=docker/dockerfile:1
FROM coqorg/coq:8.10.2

ADD . /home/proofs
RUN sudo chown -R coq:coq /home/proofs
RUN cd /home/proofs; coq_makefile -f _CoqProject -o Makefile.coq