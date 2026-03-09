#!/usr/bin/env bash

if [ $# -ne 1 ]; then
  echo "usage: $0 <error_code>"
  exit 1
fi

code=$(( $1 ))

module=$(((code >> 0x18) & 0xFF))
domain=$(((code >> 0x10) & 0xFF))
reason=$((code & 0xFFFF))

printf "m=%d d=%d r=%d\n" "$module" "$domain" "$reason"
printf "m=0x%02X d=0x%02X r=0x%04X\n" "$module" "$domain" "$reason"
