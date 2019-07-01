FROM ubuntu:18.04 as builder
LABEL author="Abdelrahman Hosny <abdelrahman.hosny@hotmail.com>"
RUN apt-get update -qq \
 && DEBIAN_FRONTEND=noninteractive apt-get -y install --no-install-recommends \
    ca-certificates \
    clang \
    bison \
    build-essential \
    flex \
    gawk \
    git \
    libffi-dev \
    libreadline-dev \
    pkg-config \
    python3 \
    tcl-dev \
 && apt-get autoclean && apt-get clean && apt-get -y autoremove \
 && update-ca-certificates \
 && rm -rf /var/lib/apt/lists

COPY . /
RUN make \
 && make install \
 && mkdir dist && cp yosys yosys-abc yosys-config yosys-filterlib yosys-smtbmc dist/

FROM ubuntu:18.04
RUN apt-get update -qq \
 && DEBIAN_FRONTEND=noninteractive apt-get -y install --no-install-recommends \
    libreadline-dev \
    tcl-dev

COPY --from=builder /dist /build

ENV PATH /build:$PATH
RUN useradd -m yosys
USER yosys
ENTRYPOINT ["yosys"]
