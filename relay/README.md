# recon-relay

The live-event relay behind the canvas page. It is **not authoritative**: git and CI hold
the truth, and the relay only fans events out fast. One static Rust binary (about 1 MB,
musl), running on deimos behind nginx at `https://recon.knownhosts.org`.

| Endpoint | |
|---|---|
| `POST /events` | one line of compact JSON `{"id", "kind", ...}`, header `Authorization: Bearer <token>`; the principal comes from the token |
| `GET /stream` | Server-Sent Events: the last 200 events (or those after `Last-Event-ID` / `?since=`), then live |
| `GET /recent?limit=N` | the last N envelopes as a JSON array |
| `GET /health` | `ok seq=<n> listeners=<n>` |

Design: the request body is never re-encoded. Each event is one `Arc<Frame>` (a small
envelope head, the original body `Bytes`, a tail) shared by every subscriber through
`tokio::sync::broadcast` and appended to `events.jsonl`; replays after a restart are
slices of one file buffer. Measured locally: 7.4 MB RSS with 200 open listeners.

## Publishers

`/etc/recon-relay/tokens` (root, 0600), one `principal sha256hex(token)` per line, handed
to the service by systemd `LoadCredential=`. To add a collaborator:

```sh
token=$(openssl rand -hex 32)          # send it to them privately
hash=$(printf %s "$token" | sha256sum | cut -d' ' -f1)
ssh root@deimos.knownhosts.org "echo '<handle> $hash' >> /etc/recon-relay/tokens && systemctl restart recon-relay"
```

To revoke, delete the line and restart.

## Deploy

- First time: `relay/bootstrap.sh`, run by a human. It sets up the tokens, the GitHub secret
  `RECON_LIVE_TOKEN`, DNS, the certificate and the first deploy.
- Updates: `relay/deploy.sh`. `relay/deploy.sh --check` shows the health.

## Rollback

```sh
ssh root@deimos.knownhosts.org '
  systemctl disable --now recon-relay
  rm -f /etc/nginx/sites-enabled/recon.knownhosts.org.conf && nginx -t && systemctl reload nginx
  pdnsutil delete-rrset knownhosts.org recon A; pdnsutil delete-rrset knownhosts.org recon AAAA
  pdnsutil rectify-zone knownhosts.org; pdnsutil increase-serial knownhosts.org
  certbot delete --cert-name recon.knownhosts.org
  rm -rf /opt/recon-relay /etc/recon-relay /etc/systemd/system/recon-relay.service'
```
