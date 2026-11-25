#!/bin/sh
# Build recon-relay and (re)deploy it to deimos. Idempotent.
#
#   relay/deploy.sh            build, copy binary + unit + vhost, restart
#   relay/deploy.sh --check    only show what is deployed
#
# First-time steps (DNS record, certificate, tokens file) are in relay/README.md.
set -eu
HOST=${RECON_RELAY_HOST:-root@deimos.knownhosts.org}
cd "$(dirname "$0")"

if [ "${1:-}" = "--check" ]; then
    ssh "$HOST" 'systemctl is-active recon-relay; curl -s http://127.0.0.1:8090/health'
    exit 0
fi

cargo build --release --target x86_64-unknown-linux-musl
BIN=target/x86_64-unknown-linux-musl/release/recon-relay

ssh "$HOST" 'install -d -m 755 /opt/recon-relay && install -d -m 700 /etc/recon-relay'
scp -q "$BIN" "$HOST":/opt/recon-relay/recon-relay.new
scp -q recon-relay.service "$HOST":/etc/systemd/system/recon-relay.service
scp -q recon.knownhosts.org.conf "$HOST":/etc/nginx/sites-available/recon.knownhosts.org.conf
ssh "$HOST" '
    set -e
    chmod 755 /opt/recon-relay/recon-relay.new
    mv /opt/recon-relay/recon-relay.new /opt/recon-relay/recon-relay
    test -f /etc/recon-relay/tokens || { echo "missing /etc/recon-relay/tokens (see relay/README.md)"; exit 1; }
    systemctl daemon-reload
    systemctl enable --quiet recon-relay
    systemctl restart recon-relay
    if [ -f /etc/letsencrypt/live/recon.knownhosts.org/fullchain.pem ]; then
        ln -sf /etc/nginx/sites-available/recon.knownhosts.org.conf /etc/nginx/sites-enabled/
        nginx -t -q && systemctl reload nginx
    else
        echo "no certificate yet: vhost not enabled (see relay/README.md)"
    fi
    sleep 1
    systemctl is-active recon-relay
    curl -s http://127.0.0.1:8090/health
'
