module

public import UUID.Basic
public import UUID.Bytes
public import UUID.Format
public import UUID.Parse
public import UUID.Literal
public import UUID.Random
public import UUID.NameBased
public import UUID.UnixTime

/-!
# UUID

[RFC 9562](https://www.rfc-editor.org/rfc/rfc9562) universally unique identifiers.

```
import UUID

#eval UUID.v4                                   -- random
#eval UUID.v7                                   -- time-ordered
#eval UUID.v5 UUID.namespaceDNS "example.com"   -- name-based
#eval UUID.parse? "f81d4fae-7dec-11d0-a765-00a0c91e6bf6"
#check uuid!"f81d4fae-7dec-11d0-a765-00a0c91e6bf6"   -- checked at compile time
```
-/
