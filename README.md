# prove-2025

**prove** stands for **Pro**gram **Ve**rification.

## Quick Start

Fetch the submodules after cloning this repo:

```
git submodule init
git submodule update
```

In directory `monadlib`, add a `CONFIGURE` file:

```
COQBIN=/home/venillalemon/.opam/default/bin/
SUF=
SL_DIR=/home/venillalemon/FV/prove-2025/qcp-docker/SeparationLogic/
COMMON_STRATEGY_DIR=/home/venillalemon/FV/prove-2025/qcp-docker/common/
```

Then follow the instructions in `monadlib`, `qcp-docker` and `qcp`.

## 关于 _CoqProject

请注意，`_CoqProject` 中 physical path 不能以 `/` 结尾，例如 `-R qcp/sll SimpleC.EE` 不能写为 `-R qcp/sll/ SimpleC.EE`，否则会出现问题。
