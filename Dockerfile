FROM ubuntu:24.04

RUN apt-get update

RUN apt-get install --assume-yes wget

RUN apt-get install --assume-yes make

RUN apt-get install --assume-yes gcc

RUN apt-get install --assume-yes time

RUN apt-get install --assume-yes libgmp-dev

RUN apt-get install --assume-yes opam build-essential m4 jq

RUN opam init -y --disable-sandboxing --compiler=5.2.0

RUN opam install ocamlfind

RUN cd /home/ubuntu/; wget https://github.com/MLton/mlton/releases/download/on-20241230-release/mlton-20241230-1.amd64-linux.ubuntu-24.04_static.tgz; tar -xvf mlton-20241230-1.amd64-linux.ubuntu-24.04_static.tgz; cd mlton-20241230-1.amd64-linux.ubuntu-24.04_static; make install; cd ../; mkdir PriML-DFC; cd PriML-DFC; mkdir priml; mkdir priml-examples; mkdir sml-lib; cd ../; mkdir domainslib

COPY priml/ /home/ubuntu/PriML-DFC/priml/

COPY priml-examples/ /home/ubuntu/PriML-DFC/priml-examples/

COPY sml-lib/ /home/ubuntu/PriML-DFC/sml-lib/

COPY Makefile README.md /home/ubuntu/PriML-DFC/

COPY scripts/ /home/ubuntu/PriML-DFC

COPY domainslib/ /home/ubuntu/domainslib/

RUN cd /home/ubuntu/domainslib; opam pin add -y domainslib file://`pwd`

RUN opam install domainslib

WORKDIR /home/ubuntu/PriML-DFC

RUN make