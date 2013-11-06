#!/bin/bash
lhs2TeX --poly Main.lhs > Main.tex
pdflatex Main.tex