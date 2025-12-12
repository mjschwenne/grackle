{
  stdenv,
  perennial,
  perennialPkgs,
  ...
}: let
  rocqv = "9.1.0";
in
  stdenv.mkDerivation {
    pname = "grackle-rocq-build";
    version = "unstable";

    src = ../../.;

    nativeBuildInputs = with perennialPkgs; [
      rocq-runtime
      rocq-stdlib
    ];
    buildInputs = with perennialPkgs; [
      coq-coqutil
      coq-record-update
      rocq-stdpp
      rocq-iris
      iris-named-props
      perennial
    ];

    buildPhase = ''
      export ROCQPATH=$COQPATH
      unset COQPATH
      make -j$NIX_BUILD_CORES
    '';

    installPhase = ''
      mkdir -p $out/lib/coq/${rocqv}/user-contrib/Grackle
      mkdir -p $out/lib/coq/${rocqv}/user-contrib/New
      cp -r example/proof $out/lib/coq/${rocqv}/user-contrib/Grackle/example
      cp -r example/goose $out/lib/coq/${rocqv}/user-contrib/New/code
      cp -r testdata/out/pg $out/lib/coq/${rocqv}/user-contrib/New/generatedproof
      cp -r testdata/out/goose $out/lib/coq/${rocqv}/user-contrib/New/code
      cp -r testdata/out/rocq $out/lib/coq/${rocqv}/user-contrib/Grackle/test
    '';
  }
