FROM ubuntu:22.04
WORKDIR /usr/local/kemedhoc

# Install dependencies
COPY install_deps.sh ./
RUN apt update
RUN apt install -y curl build-essential \
    && chmod +x install_deps.sh && ./install_deps.sh

# Copy source code
COPY src ./src

# Copy external libraries
COPY external-libs ./external-libs

# Copy uedhoc
COPY pq-uoscore-uedhoc ./pq-uoscore-uedhoc

# Copy Proverif models
COPY pv-models ./pv-models

# Verify and compile HACL*
CMD [ "make", "-C", "external-libs/hacl-star" ]
