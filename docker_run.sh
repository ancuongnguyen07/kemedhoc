#! /bin/bash
set -e

docker build -t kemedhoc:1.0 .
docker run -it kemedhoc:1.0
