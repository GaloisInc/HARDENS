# HARDENS

Repository for the HARDENS project for the [Nuclear Regulatory Commission](https://www.nrc.gov/about-nrc.html).

## Submodules

Initialize with:

```
$ git submodule init
$ git submodule update --recursive
```

## Docker
Build and run with:

```
$ docker build -t hardens:latest .
$ docker run -v $PWD:/HARDENS -it hardens:latest
```
