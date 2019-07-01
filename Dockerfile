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

COPY . /

RUN make \
 && make install \
 && mkdir dist && cp yosys yosys-abc yosys-config yosys-filterlib yosys-smtbmc dist/

#---

FROM base

COPY --from=build /dist /opt/yosys

ENV PATH /opt/yosys:$PATH

RUN useradd -m yosys
USER yosys

CMD ["yosys"]
