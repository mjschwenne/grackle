{
  buildGoModule,
  protobuf,
  ...
}:
buildGoModule {
  pname = "grackle";
  version = "new";
  src = ../../.;
  vendorHash = "sha256-rVcPOrdDsBaQqkBJx2oE5ofsFJwFsSTAptq2o7rm15U=";
  nativeBuildInputs = [protobuf];
}
