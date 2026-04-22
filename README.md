# Project Title

Sorting Correctness with Dafny

## Description

This project proves corretness of sorting algorithms using Dafny. THe sorting algorithms proven are quicksort and a version of wavesort (https://arxiv.org/pdf/2505.13552) with a simplified block swap implementation. quicksort3.dfy contains a proof of correctness for quicksort. wavesort.dfy contains a proof of correctness for wavesort. Future work to prove the smaller left block swap implementation as shown on arxiv.

## Getting Started

### Dependencies

Dafny (https://dafny.org)

### Executing program

To run dafny verification, run the following commands from the command line:

```
dafny verify quicksort3.dfy
```

```
dafny verify wavesort.dfy
```

## Authors

Trent Hamilton
