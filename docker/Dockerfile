FROM ubuntu:bionic

WORKDIR /app

RUN ["apt-get", "update"]
RUN ["apt-get", "upgrade", "-y"]

RUN ["apt-get", "install", "-y", "g++", "git", "cmake", "libgmp-dev", "wget"]

RUN ["wget", "https://bitbucket.org/eigen/eigen/get/3.3.7.tar.gz"]
RUN ["tar", "-xzvf", "3.3.7.tar.gz"]

WORKDIR /app/eigen-eigen-323c052e1731
RUN ["mkdir", "build"]
WORKDIR /app/eigen-eigen-323c052e1731/build
RUN ["cmake", ".."]
RUN ["make", "install"]

WORKDIR /app
RUN ["git", "clone", "https://github.com/dselsam/lean.git"]
WORKDIR /app/lean
RUN ["git", "checkout", "certigrad"]
RUN ["mkdir", "-p", "build/release"]
WORKDIR /app/lean/build/release
RUN ["cmake", "../../src"]
RUN ["make", "-j4"]
RUN ["make", "install"]

WORKDIR /app

RUN ["git", "clone", "https://github.com/dselsam/certigrad.git"]
WORKDIR /app/certigrad
RUN ["leanpkg", "build"]
