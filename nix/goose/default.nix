{
  buildGoModule,
  fetchFromGitHub,
}: let
  pname = "goose";
  version = "0.9.2-unstable-2025-08-20";
  src = fetchFromGitHub {
    owner = "goose-lang";
    repo = "goose";
    rev = "b49ba60dd19a5e2c72321c5e8854f03c3683ec75";
    hash = "sha256-vGY7A276//4mG9X7PsUEdwigglwjL4di9g7Wi18qesY=";
  };
in
  buildGoModule {
    inherit pname version src;
    proxyVendor = true;
    vendorHash = "sha256-MHo+sm5MUP5NVn128vu02zVcs2gpg24zC8o+UvBOnpI=";
  }
