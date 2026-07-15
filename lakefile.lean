import Lake
open Lake DSL

package «ProveFalseTest» {
  -- add package configuration options here
}

@[default_target]
lean_exe «ProveFalseTest» {
  root := `ProveFalse
}
