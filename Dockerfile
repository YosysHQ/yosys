ARG IMAGE="ubuntu:18.04"

#---

FROM $IMAGE AS base

RUN apt-get update -qq \
 && DEBIAN_FRONTEND=noninteractive apt-get -y install --no-install-recommends \
    ca-certificates \
    libreadline-dev \
    tcl-dev \
 && apt-get autoclean && apt-get clean && apt-get -y autoremove \
 && update-ca-certificates \
 && rm -rf /var/lib/apt/lists

#---

FROM base AS build

RUN apt-get update -qq \
 && DEBIAN_FRONTEND=noninteractive apt-get -y install --no-install-recommends \
    clang \
    bison \
    build-essential \
    flex \
    gawk \
    git \
    libffi-dev \
    pkg-config \
    python3 \
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
