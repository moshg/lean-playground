import UUID

/-!
# Compile-time tests

Every `#guard` here is checked when the test executable is *built*, so these double as
regression tests for the pure API. Test vectors come from RFC 9562 Appendix A/B, the Python
`uuid` documentation, RFC 1321 (MD5) and RFC 3174 / FIPS 180 (SHA-1).
-/

open UUID

/-! ## Special values -/

#guard UUID.nil.toString = "00000000-0000-0000-0000-000000000000"
#guard UUID.max.toString = "ffffffff-ffff-ffff-ffff-ffffffffffff"
#guard UUID.nil.isNil && !UUID.max.isNil && UUID.max.isMax
#guard UUID.nil.version? = none
#guard UUID.max.version? = none
#guard UUID.nil.variant = .ncs
#guard UUID.max.variant = .future
#guard UUID.nil < UUID.max
#guard (default : UUID) = UUID.nil

/-! ## RFC 9562 examples -/

-- Appendix A.1: UUIDv1
#guard (uuid!"C232AB00-9414-11EC-B3C8-9F6BDECED846").version? = some .gregorian
-- Appendix A.2: UUIDv3
#guard UUID.v3 UUID.namespaceDNS "www.example.com" = uuid!"5df41881-3aed-3515-88a7-2f4a814cf09e"
-- Appendix A.3: UUIDv4
#guard (uuid!"919108f7-52d1-4320-9bac-f847db4148a8").version? = some .random
-- Appendix A.4: UUIDv5
#guard UUID.v5 UUID.namespaceDNS "www.example.com" = uuid!"2ed6657d-e927-568b-95e1-2665a8aea6a2"
-- Appendix A.5: UUIDv6
#guard (uuid!"1EC9414C-232A-6B00-B3C8-9F6BDECED846").version? = some .reorderedGregorian
-- Appendix A.6: UUIDv7
#guard UUID.v7Of 0x017F22E279B0 0xCC3 0x18C4DC0C0C07398F =
  uuid!"017F22E2-79B0-7CC3-98C4-DC0C0C07398F"
#guard (uuid!"017F22E2-79B0-7CC3-98C4-DC0C0C07398F").unixTimeMs? = some 0x017F22E279B0
-- Appendix B.1/B.2: UUIDv8
#guard (uuid!"2489E9AD-2EE2-8E00-8EC9-32D5F69181C0").version? = some .custom
#guard (uuid!"5c146b14-3c52-8afd-938a-375d0df1fbf6").version? = some .custom

/-! ## Python `uuid` documentation examples -/

#guard UUID.v3 UUID.namespaceDNS "python.org" = uuid!"6fa459ea-ee8a-3ca4-894e-db77e160355e"
#guard UUID.v5 UUID.namespaceDNS "python.org" = uuid!"886313e1-3b8a-5372-9b90-0c9aee199e5d"

-- Cross-checked against Python's `uuid.uuid3` / `uuid.uuid5`
#guard UUID.v3 UUID.namespaceURL "https://example.com/" =
  uuid!"b9dcdff8-af4a-365d-8043-0f8361942709"
#guard UUID.v5 UUID.namespaceURL "https://example.com/" =
  uuid!"dd2c1780-811a-5296-81c5-178a0ef488bc"
#guard UUID.v3 UUID.namespaceOID "1.3.6.1" = uuid!"dd1a1cef-13d5-368a-ad82-eca71acd4cd1"
#guard UUID.v5 UUID.namespaceOID "1.3.6.1" = uuid!"1447fa61-5277-5fef-a9b3-fbc6e44f4af3"
#guard UUID.v3 UUID.namespaceX500 "cn=John Doe, o=Acme" =
  uuid!"72c5d676-04d5-34a2-8333-6d7cdd991933"
#guard UUID.v5 UUID.namespaceX500 "cn=John Doe, o=Acme" =
  uuid!"987fc182-403d-5310-907a-892579ca3c81"
#guard UUID.v3 UUID.namespaceDNS "日本語.jp" = uuid!"863baec1-4e0b-3bf6-9ceb-d56aba2a8328"
#guard UUID.v5 UUID.namespaceDNS "日本語.jp" = uuid!"ece9716c-4041-5412-9787-9304e06f91a8"
#guard UUID.v3 UUID.namespaceDNS "" = uuid!"c87ee674-4ddc-3efe-a74e-dfe25da5d7b3"
#guard UUID.v5 UUID.namespaceDNS "" = uuid!"4ebd0208-8328-5d69-8c44-ec50939c0967"

/-! ## Namespaces -/

#guard UUID.namespaceDNS.toString = "6ba7b810-9dad-11d1-80b4-00c04fd430c8"
#guard UUID.namespaceURL.toString = "6ba7b811-9dad-11d1-80b4-00c04fd430c8"
#guard UUID.namespaceOID.toString = "6ba7b812-9dad-11d1-80b4-00c04fd430c8"
#guard UUID.namespaceX500.toString = "6ba7b814-9dad-11d1-80b4-00c04fd430c8"

/-! ## Formatting -/

section
private def sample : UUID := uuid!"f81d4fae-7dec-11d0-a765-00a0c91e6bf6"

#guard sample.hi = 0xf81d4fae7dec11d0 && sample.lo = 0xa76500a0c91e6bf6
#guard sample.toHexString = "f81d4fae7dec11d0a76500a0c91e6bf6"
#guard sample.toUrn = "urn:uuid:f81d4fae-7dec-11d0-a765-00a0c91e6bf6"
#guard sample.toBraced = "{f81d4fae-7dec-11d0-a765-00a0c91e6bf6}"
#guard s!"{sample}" = "f81d4fae-7dec-11d0-a765-00a0c91e6bf6"
#guard reprStr sample = "uuid!\"f81d4fae-7dec-11d0-a765-00a0c91e6bf6\""
#guard sample.toBytes.toList =
  [0xf8, 0x1d, 0x4f, 0xae, 0x7d, 0xec, 0x11, 0xd0, 0xa7, 0x65, 0x00, 0xa0, 0xc9, 0x1e, 0x6b, 0xf6]
#guard sample.toNat = 0xf81d4fae7dec11d0a76500a0c91e6bf6
#guard UUID.ofNat 0xf81d4fae7dec11d0a76500a0c91e6bf6 = sample

/-! ## Parsing -/

#guard UUID.parse? "f81d4fae-7dec-11d0-a765-00a0c91e6bf6" = some sample
#guard UUID.parse? "F81D4FAE-7DEC-11D0-A765-00A0C91E6BF6" = some sample
#guard UUID.parse? "f81d4fae7dec11d0a76500a0c91e6bf6" = some sample
#guard UUID.parse? "{f81d4fae-7dec-11d0-a765-00a0c91e6bf6}" = some sample
#guard UUID.parse? "{f81d4fae7dec11d0a76500a0c91e6bf6}" = some sample
#guard UUID.parse? "urn:uuid:f81d4fae-7dec-11d0-a765-00a0c91e6bf6" = some sample
#guard UUID.parse? "URN:UUID:f81d4fae-7dec-11d0-a765-00a0c91e6bf6" = some sample
#guard uuid!"{F81D4FAE7DEC11D0A76500A0C91E6BF6}" = sample
end

/-- The error reported when parsing `s`, if any. -/
def parseError (s : String) : Option ParseError :=
  match UUID.parse s with
  | .ok _ => none
  | .error e => some e

#guard parseError "" = some (.invalidLength 0)
#guard parseError "f81d4fae-7dec-11d0-a765-00a0c91e6bf" = some (.invalidLength 35)
#guard parseError "f81d4fae-7dec-11d0-a765-00a0c91e6bf6a" = some (.invalidLength 37)
#guard parseError "{f81d4fae-7dec-11d0-a765-00a0c91e6bf6" = some (.invalidLength 37)
#guard parseError "f81d4fae-7dec-11d0-a765-00a0c91e6bfg" = some (.invalidChar 'g' 35)
#guard parseError "f81d4fae_7dec-11d0-a765-00a0c91e6bf6" = some (.invalidChar '_' 8)
#guard parseError "f81d4fae7-dec-11d0-a765-00a0c91e6bf6" = some (.invalidChar '7' 8)
#guard parseError "{f81d4fae-7dec-11d0-a765-00a0c91e6bfx}" = some (.invalidChar 'x' 36)
#guard parseError "urn:uuid:f81d4fae-7dec-11d0-a765+00a0c91e6bf6" = some (.invalidChar '+' 32)
#guard (parseError "f81d4fae-7dec-11d0-a765-00a0c91e6bf６").isSome

/-! ## Bytes -/

#guard UUID.ofByteArray? (ByteArray.mk #[1, 2, 3]) = none
#guard UUID.ofByteArray? (UUID.namespaceDNS.toByteArray) = some UUID.namespaceDNS

/-! ## Version and variant -/

#guard (UUID.v8Of UUID.max).version? = some .custom
#guard (UUID.v8Of UUID.max).toString = "ffffffff-ffff-8fff-bfff-ffffffffffff"
#guard (UUID.v4Of UUID.nil).toString = "00000000-0000-4000-8000-000000000000"
#guard (uuid!"00000000-0000-0000-c000-000000000000").variant = .microsoft
#guard (uuid!"00000000-0000-0000-e000-000000000000").variant = .future
#guard (uuid!"00000000-0000-9000-8000-000000000000").version? = none  -- undefined version 9

/-! ## Ordering -/

#guard uuid!"00000000-0000-0000-0000-000000000001" < uuid!"00000000-0000-0000-0000-000000000002"
#guard uuid!"00000000-0000-0001-0000-000000000000" > uuid!"00000000-0000-0000-ffff-ffffffffffff"
#guard compare UUID.namespaceDNS UUID.namespaceDNS = .eq
#guard Max.max UUID.namespaceDNS UUID.namespaceURL = UUID.namespaceURL

/-! ## Monotonic v7 counter -/

-- rand_b increments
#guard V7.succ (UUID.v7Of 1 0 0) = UUID.v7Of 1 0 1
-- rand_b overflows into rand_a
#guard V7.succ (UUID.v7Of 1 0 0x3FFFFFFFFFFFFFFF) = UUID.v7Of 1 1 0
-- rand_a overflows into the timestamp
#guard V7.succ (UUID.v7Of 1 0xFFF 0x3FFFFFFFFFFFFFFF) = UUID.v7Of 2 0 0
-- the clock going backwards still yields an increasing UUID
#guard V7.next (UUID.v7Of 1000 5 5) 999 7 7 = UUID.v7Of 1000 5 6
-- a later timestamp wins
#guard V7.next (UUID.v7Of 1000 5 5) 1001 0 0 = UUID.v7Of 1001 0 0

/-! ## Hash functions -/

open UUID.Hash in
section
#guard toHex (md5 "".toUTF8) = "d41d8cd98f00b204e9800998ecf8427e"
#guard toHex (md5 "abc".toUTF8) = "900150983cd24fb0d6963f7d28e17f72"
#guard toHex (md5 "The quick brown fox jumps over the lazy dog".toUTF8) =
  "9e107d9d372bb6826bd81d3542a419d6"
#guard toHex (md5 (String.join (List.replicate 8 "1234567890")).toUTF8) =
  "57edf4a22be3c955ac49da2e2107b67a"
#guard toHex (sha1 "".toUTF8) = "da39a3ee5e6b4b0d3255bfef95601890afd80709"
#guard toHex (sha1 "abc".toUTF8) = "a9993e364706816aba3e25717850c26c9cd0d89d"
#guard toHex (sha1 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8) =
  "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
#guard toHex (sha1 "The quick brown fox jumps over the lazy dog".toUTF8) =
  "2fd4e1c67a2d28fced849ee1bb76e7391b93eb12"
-- "a" * n for lengths around the 55/56/64-byte padding boundaries (computed with Python hashlib)
private def as (n : Nat) : ByteArray := (String.ofList (List.replicate n 'a')).toUTF8
#guard [55, 56, 63, 64, 65, 119, 120].map (toHex ∘ md5 ∘ as) = [
  "ef1772b6dff9a122358552954ad0df65", "3b0c8ac703f828b04c6c197006d17218",
  "b06521f39153d618550606be297466d5", "014842d480b571495a4a0363793f7367",
  "c743a45e0d2e6a95cb859adae0248435", "8a7bd0732ed6a28ce75f6dabc90e1613",
  "5f61c0ccad4cac44c75ff505e1f1e537"]
#guard [55, 56, 63, 64, 65, 119, 120].map (toHex ∘ sha1 ∘ as) = [
  "c1c8bbdc22796e28c0e15163d20899b65621d65a", "c2db330f6083854c99d4b5bfb6e8f29f201be699",
  "03f09f5b158a7a8cdad920bddc29b81c18a551f5", "0098ba824b5c16427bd7a1122a5a442a25ec644d",
  "11655326c708d70319be2610e8a57d9a5b959d3b", "ee971065aaa017e0632a8ca6c77bb3bf8b1dfc56",
  "f34c1488385346a55709ba056ddd08280dd4c6d6"]
end
