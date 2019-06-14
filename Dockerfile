FROM ubuntu:18.04 as builder
LABEL author="Abdelrahman Hosny <abdelrahman.hosny@hotmail.com>"
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y build-essential \
    clang \
    bison \
    flex \
    libreadline-dev \
    gawk \
    tcl-dev \
    libffi-dev \
    git \
    pkg-config \
    python3 && \
    rm -rf /var/lib/apt/lists
COPY . /
RUN make && \
    make install

FROM ubuntu:18.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y libreadline-dev tcl-dev

COPY --from=builder /yosys /build/yosys
COPY --from=builder /yosys-abc /build/yosys-abc
COPY --from=builder /yosys-config /build/yosys-config
COPY --from=builder /yosys-filterlib /build/yosys-filterlib
COPY --from=builder /yosys-smtbmc /build/yosys-smtbmc

ENV PATH /build:$PATH
RUN useradd -m yosys
USER yosys
ENTRYPOINT ["yosys"]
