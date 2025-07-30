# Use OCaml/OPAM base image with OCaml preinstalled
FROM ocaml/opam:ubuntu-22.04-ocaml-5.2
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN sudo apt-get update && sudo apt-get install -y \
    build-essential \
    git \
    curl \
    pkg-config \
    libgmp-dev \
    python3 \
    python3-pip \
    && sudo rm -rf /var/lib/apt/lists/*

# Update OPAM and install packages (single layer, eval env)
RUN opam update && \
    eval $(opam env) && \
    opam install -y dune reason incr_dom ocaml-lsp-server core_unix ocaml_intrinsics pprint

RUN pip install matplotlib dominate

# Copy project files
COPY . /app
WORKDIR /app
RUN sudo chown -R opam:opam /app

# Build the project using opam env
RUN eval $(opam env) && make build

EXPOSE 8000

# Serve using make serve, with opam env activated
CMD eval $(opam env) && python3 -m http.server 8000