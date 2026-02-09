import sys

def from_err_code(code: int) -> tuple[int, int, int]:
    reason = code & 0xFFFF
    domain = (code >> 16) & 0xFF
    module = (code >> 24) & 0xFF
    
    return module, domain, reason

def main() -> None:
    if len(sys.argv) != 2:
        sys.exit("usage: <bin> <error_code>")

    try:
        code = int(sys.argv[1], 0)
    except ValueError:
        sys.exit("invalid error code")

    module, domain, reason = from_err_code(code)
    print(
        f"code=0x{code:08X} "
        f"module={module} "
        f"domain={domain} "
        f"reason={reason}"
    )

if __name__ == "__main__":
    main()
