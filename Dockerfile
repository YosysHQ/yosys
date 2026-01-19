ARG IMAGE="python:3-slim-buster"

#---

FROM $IMAGE AS base

RUN apt-get update -qq \
 && DEBIAN_FRONTEND=noninteractive apt-get -y install --no-install-recommends \
    ca-certificates \
    clang \
    lld \
    curl \
    libffi-dev \
    libreadline-dev \
    tcl-dev \
    graphviz \
    xdot \
 && apt-get autoclean && apt-get clean && apt-get -y autoremove \
 && update-ca-certificates \
 && rm -rf /var/lib/apt/lists

#---

FROM base AS build

RUN apt-get update -qq \
 && DEBIAN_FRONTEND=noninteractive apt-get -y install --no-install-recommends \
    bison \
    flex \
    gawk \
    gcc \
    git \
    iverilog \
    pkg-config \
 && apt-get autoclean && apt-get clean && apt-get -y autoremove \
 && rm -rf /var/lib/apt/lists

COPY . /yosys

ENV PREFIX /opt/yosys

RUN cd /yosys \
 && make \
 && make install \
 && make test

#---

FROM base

COPY --from=build /opt/yosys /opt/yosys

ENV PATH /opt/yosys/bin:$PATH

RUN useradd -m yosys
USER yosys

CMD ["yosys"]
