#!/bin/sh

echo "=== when failed to maintain:  pre => Inv "
mono ./Boogie.exe -nologo -normalArg -noinfer -contractInfer -errorTrace:0 -mlHoudini:ice   ice_pre.bpl

echo "=== when failed to be inductive:  Inv & B {S} => Inv "
mono ./Boogie.exe -nologo -normalArg -noinfer -contractInfer -errorTrace:0 -mlHoudini:ice   ice_loop.bpl

echo "=== when failed to derive post condition: not B & Inv => post"
mono ./Boogie.exe -nologo -normalArg -noinfer -contractInfer -errorTrace:0 -mlHoudini:ice   ice_post.bpl
