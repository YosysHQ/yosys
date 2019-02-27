FROM ubuntu:16.04 as builder
LABEL author="Abdelrahman Hosny <abdelrahman.hosny@hotmail.com>"

RUN apt-get update && apt-get install -y build-essential \
    clang \
    bison \
    flex \
    libreadline-dev \
    gawk \
    tcl-dev \
    libffi-dev \
    git \
    graphviz \
    xdot \
    pkg-config \
    python3

COPY . /
RUN make && \
    make install


FROM ubuntu:16.04
RUN apt-get update && apt-get install -y clang \
    bison \
    flex \
    libreadline-dev \
    gawk \
    tcl-dev \
    libffi-dev \
    git \
    graphviz \
    xdot \
    pkg-config \
    python3
COPY --from=builder /yosys /build/yosys
COPY --from=builder /yosys-abc /build/yosys-abc
COPY --from=builder /yosys-config /build/yosys-config
COPY --from=builder /yosys-filterlib /build/yosys-filterlib
COPY --from=builder /yosys-smtbmc /build/yosys-smtbmc

ENV PATH /build:$PATH

RUN mkdir /data
WORKDIR /data

ENTRYPOINT ["yosys"]
