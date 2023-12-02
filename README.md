<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Parseque

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/parseque/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/parseque/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



Port of the agdarsec total parser combinator library to Coq.

## Meta

- Author(s):
  - G. Allais (initial)
- Coq-community maintainer(s):
  - Wolfgang Meier ([**@womeier**](https://github.com/womeier))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.16 or later
- Additional dependencies: none
- Coq namespace: `parseque`
- Related publication(s):
  - [agdarsec - Total Parser Combinators](https://gallais.github.io/pdf/agdarsec18.pdf) 

## Building and installation instructions

The easiest way to install the latest released version of Parseque
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-parseque
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/parseque.git
cd parseque
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

This Coq library is a port of the [agdarsec](https://github.com/gallais/agdarsec)
library for Agda. The core design of agdarsec is described in
[this paper](https://gallais.github.io/pdf/agdarsec18.pdf), while
[this blog post](https://gallais.github.io/blog/instrumenting-agdarsec)
describes instrumentation.
