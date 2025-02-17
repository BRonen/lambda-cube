{ pkgs ? import <nixpkgs> { } }:
with pkgs; mkShell {
  buildInputs = [ lean4 ];
}
