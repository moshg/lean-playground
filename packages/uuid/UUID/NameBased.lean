module

public import UUID.Bytes
public import UUID.Hash.MD5
public import UUID.Hash.SHA1

/-!
# Name-based UUIDs (versions 3 and 5)

A name-based UUID is derived deterministically from a *namespace* UUID and a *name*
(RFC 9562 §5.3, §5.5): the same namespace and name always produce the same UUID.

```
UUID.v5 UUID.namespaceDNS "www.example.com" = uuid!"2ed6657d-e927-568b-95e1-2665a8aea6a2"
```

Prefer version 5 (SHA-1) over version 3 (MD5) for new applications.
-/

@[expose] public section

namespace UUID

/-! ## Well-known namespaces (RFC 9562 §6.6) -/

/-- Namespace for fully-qualified domain names: `6ba7b810-9dad-11d1-80b4-00c04fd430c8`. -/
def namespaceDNS : UUID := ⟨0x6ba7b8109dad11d1, 0x80b400c04fd430c8⟩

/-- Namespace for URLs: `6ba7b811-9dad-11d1-80b4-00c04fd430c8`. -/
def namespaceURL : UUID := ⟨0x6ba7b8119dad11d1, 0x80b400c04fd430c8⟩

/-- Namespace for ISO OIDs: `6ba7b812-9dad-11d1-80b4-00c04fd430c8`. -/
def namespaceOID : UUID := ⟨0x6ba7b8129dad11d1, 0x80b400c04fd430c8⟩

/-- Namespace for X.500 distinguished names: `6ba7b814-9dad-11d1-80b4-00c04fd430c8`. -/
def namespaceX500 : UUID := ⟨0x6ba7b8149dad11d1, 0x80b400c04fd430c8⟩

/-! ## Construction -/

/-- The UUID formed by the first 16 octets of a digest (which must be at least 16 bytes). -/
def ofDigest (digest : ByteArray) : UUID :=
  (ofByteArray? (digest.extract 0 16)).getD nil

/-- A version 3 UUID from a namespace and a name given as raw bytes. -/
def v3Bytes (ns : UUID) (name : ByteArray) : UUID :=
  (ofDigest (Hash.md5 (ns.toByteArray ++ name))).withVersion .md5

/-- A version 3 (MD5, name-based) UUID. The name is encoded as UTF-8. -/
def v3 (ns : UUID) (name : String) : UUID :=
  v3Bytes ns name.toUTF8

/-- A version 5 UUID from a namespace and a name given as raw bytes. -/
def v5Bytes (ns : UUID) (name : ByteArray) : UUID :=
  (ofDigest (Hash.sha1 (ns.toByteArray ++ name))).withVersion .sha1

/-- A version 5 (SHA-1, name-based) UUID. The name is encoded as UTF-8. -/
def v5 (ns : UUID) (name : String) : UUID :=
  v5Bytes ns name.toUTF8

@[simp] theorem version?_v3 (ns : UUID) (name : String) : (v3 ns name).version? = some .md5 := by
  simp [v3, v3Bytes]

@[simp] theorem version?_v5 (ns : UUID) (name : String) : (v5 ns name).version? = some .sha1 := by
  simp [v5, v5Bytes]

end UUID

end
