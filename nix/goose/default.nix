{
  buildGoModule,
  fetchFromGitHub,
}: let
  pname = "goose";
  version = "0.9.2-unstable-2025-09-04";
  src = fetchFromGitHub {
    owner = "goose-lang";
    repo = "goose";
    rev = "5db12193b2b38ce47516e76e156db5ee11d300e3";
    hash = "sha256-9XZRJNSbu/IS+fk0EIWC0CfkHJigsqQDVH0E+ffaAGU=";
  };
in
  buildGoModule {
    inherit pname version src;
    proxyVendor = true;
    vendorHash = "sha256-MHo+sm5MUP5NVn128vu02zVcs2gpg24zC8o+UvBOnpI=";
  }
