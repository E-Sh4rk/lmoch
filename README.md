# lmoch (Model Checker for Lustre)

https://www.di.ens.fr/~pouzet/cours/mpri/projet/lmoch.pdf

## How to compile

Use ``make`` in this directory.
It will compile AEZ and the model checker.

Note: I have modified AEZ, so if you want to compile it manually, please replace the file ``vec.ml``
by the modified version ``lib/vec.ml``.
See the report for more information.

## How to test

Go into the directory ``examples`` (initial examples) or ``demo`` (some new examples that I have added).
Then you can test the model checker by doing ``make check FILE=example.lus``.