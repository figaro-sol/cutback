RUST_LOG='codex_api::sse::responses=trace' codex exec --sandbox read-only --model gpt-5.3-codex 'ping' 2>&1
| grep -m1 'SSE event: {"type":"response.created"'
| sed 's/.*SSE event: //'
| jq -r '.response.model'
