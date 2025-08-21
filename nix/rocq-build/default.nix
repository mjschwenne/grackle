{
  stdenv,
  rocq-core,
  rocqPackages,
  perennial,
  ...
}: let
  rocqv = rocq-core.rocq-version;
in
  stdenv.mkDerivation {
    pname = "grackle-rocq-build";
    version = "unstable";

    src = ../../.;

    buildInputs = [
      rocq-core
      rocqPackages.stdlib
      perennial
    ];

    ROCQPATH = ''
      ${perennial}/lib/coq/${rocqv}/user-contrib:$ROCQPATH
    '';

    buildPhase = ''
      make -j$NIX_BUILD_CORES
    '';

    installPhase = ''
      mkdir -p $out/lib/coq/${rocqv}/user-contrib/Grackle
      mkdir -p $out/lib/coq/${rocqv}/user-contrib/New
      cp -r example/proof $out/lib/coq/${rocqv}/user-contrib/Grackle/example
      cp -r example/goose $out/lib/coq/${rocqv}/user-contrib/New/code
      cp -r testdata/out/pg $out/lib/coq/${rocqv}/user-contrib/New/generatedproof
      cp -r testdata/out/goose $out/lib/coq/${rocqv}/user-contrib/New/code
      cp -r testdata/out/coq $out/lib/coq/${rocqv}/user-contrib/Grackle/test
    '';
  }
