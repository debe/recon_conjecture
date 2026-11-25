#!/bin/sh
# First-time setup of the live relay on deimos. Run by a human, never by an agent:
#
#   ! relay/bootstrap.sh
#
# Idempotent: every step checks before it changes anything. Steps:
#   1. publisher token for this machine     ~/.config/recon/live.token (0600)
#   2. CI publisher token                   GitHub secret RECON_LIVE_TOKEN (new token each run)
#   3. token hashes on the relay            deimos:/etc/recon-relay/tokens (only these lines replaced)
#   4. DNS                                  recon.knownhosts.org A + AAAA (PowerDNS, DNSSEC rectify)
#   5. TLS                                  certbot certonly --webroot
#   6. deploy                               relay/deploy.sh
# Rollback: see relay/README.md.
set -eu
HOST=${RECON_RELAY_HOST:-root@deimos.knownhosts.org}
REPO=${RECON_REPO:-debe/recon_conjecture}
GH_USER=${RECON_GH_USER:-debe}
ME=$(git config recon.handle || echo "$GH_USER")
IPV4=159.69.52.85
IPV6=2a01:4f8:c17:aaa6::1
cd "$(dirname "$0")"
step() { printf '\n== %s\n' "$*"; }

step "1/6 publisher token for $ME"
mkdir -p "$HOME/.config/recon" && chmod 700 "$HOME/.config/recon"
TOKEN_FILE="$HOME/.config/recon/live.token"
if [ ! -s "$TOKEN_FILE" ]; then
    (umask 077 && openssl rand -hex 32 | tr -d '\n' > "$TOKEN_FILE")
    echo "created $TOKEN_FILE"
else
    echo "kept $TOKEN_FILE"
fi
H_ME=$(sha256sum < "$TOKEN_FILE" | cut -d' ' -f1)

step "2/6 CI token -> GitHub secret RECON_LIVE_TOKEN on $REPO"
CI_TOKEN=$(openssl rand -hex 32)
printf %s "$CI_TOKEN" | GH_TOKEN=$(gh auth token --user "$GH_USER") gh secret set RECON_LIVE_TOKEN --repo "$REPO"
H_CI=$(printf %s "$CI_TOKEN" | sha256sum | cut -d' ' -f1)
unset CI_TOKEN

step "3/6 token hashes -> $HOST:/etc/recon-relay/tokens (lines for $ME and ci)"
# shellcheck disable=SC2029  # values expand locally on purpose
ssh "$HOST" "ME=$ME H_ME=$H_ME H_CI=$H_CI sh -s" <<'EOF'
set -eu
install -d -m 700 /etc/recon-relay
f=/etc/recon-relay/tokens
umask 077
touch "$f"
{ grep -vE "^($ME|ci)[[:space:]]" "$f" || true; echo "$ME $H_ME"; echo "ci $H_CI"; } > "$f.new"
mv "$f.new" "$f"
chmod 600 "$f"
echo "principals: $(grep -vc '^#' "$f")"
if systemctl is-active -q recon-relay; then systemctl restart recon-relay; fi
EOF

step "4/6 DNS recon.knownhosts.org"
# shellcheck disable=SC2029
ssh "$HOST" "IPV4=$IPV4 IPV6=$IPV6 sh -s" <<'EOF'
set -eu
if pdnsutil list-zone knownhosts.org | grep -qE '^recon\.knownhosts\.org\.?[[:space:]]'; then
    echo "record exists"
else
    pdnsutil add-record knownhosts.org recon A 3600 "$IPV4"
    pdnsutil add-record knownhosts.org recon AAAA 3600 "$IPV6"
    pdnsutil rectify-zone knownhosts.org
    pdnsutil increase-serial knownhosts.org
    pdns_control notify knownhosts.org
fi
pdnsutil list-zone knownhosts.org | grep -E '^recon\.knownhosts\.org\.?[[:space:]]'
EOF

step "5/6 certificate"
ssh "$HOST" 'set -eu
if [ -d /etc/letsencrypt/live/recon.knownhosts.org ]; then echo "certificate exists"; else
    certbot certonly --webroot -w /var/www/html -d recon.knownhosts.org --non-interactive --keep-until-expiring
fi'

step "6/6 deploy"
./deploy.sh

step "check"
curl -fsS https://recon.knownhosts.org/health
echo "done. Test: python3 tools/live.py emit test --note hello"
