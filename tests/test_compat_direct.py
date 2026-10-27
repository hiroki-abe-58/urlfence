"""The direct views' wire checks in tests/compat.py, on their own: the ClientHello parser on real
ClientHellos from Python's ssl module (made in memory, with no network), and what `direct_of`
reports for each kind of difference. The views themselves run in tests/compat.py, whose
`--self-test` checks that each of them reports wrong expectations."""
import os
import ssl
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import compat  # noqa: E402


def client_hello(server_hostname):
    """What a TLS client sends first, for this server_hostname (None: no name at all)."""
    context = ssl.create_default_context()
    context.check_hostname = server_hostname is not None
    out = ssl.MemoryBIO()
    tls = context.wrap_bio(ssl.MemoryBIO(), out, server_hostname=server_hostname)
    try:
        tls.do_handshake()
    except ssl.SSLWantReadError:
        pass
    return out.read()


def head(*lines):
    return ("\r\n".join(lines) + "\r\n\r\n").encode()


class ClientHello(unittest.TestCase):
    def test_server_name(self):
        for name in ["example.com", "a.b.example.com", "localhost", "a"]:
            self.assertEqual(compat.client_hello_names(client_hello(name)), [name])

    def test_no_server_name(self):
        self.assertEqual(compat.client_hello_names(client_hello(None)), [])
        self.assertEqual(compat.client_hello_names(client_hello("1.2.3.4")), [])  # RFC 6066: no address

    def test_records_and_pieces(self):
        """Complete only once all of it has arrived, also when split over several TLS records."""
        hello = client_hello("example.com")
        body = hello[5:]
        split = b"".join(hello[:3] + len(part).to_bytes(2, "big") + part
                         for part in (body[:3], body[3:100], body[100:]))
        for data in (hello, split):
            for i in range(len(data)):
                self.assertFalse(compat.message_complete(data[:i]), i)
            self.assertTrue(compat.message_complete(data))
            self.assertEqual(compat.client_hello_names(data), ["example.com"])

    def test_not_a_client_hello(self):
        hello = client_hello("example.com")
        for bad in (hello[:-1], hello[:5] + b"\x02" + hello[6:], b"\x16\x03\x01\x00\x00"):
            with self.assertRaises((ValueError, IndexError)):
                compat.client_hello_names(bad)


class DirectOf(unittest.TestCase):
    def test_https(self):
        hello, ip = client_hello("example.com"), client_hello("1.2.3.4")
        ok = ("https", "example.com", 443, "")
        self.assertEqual(compat.direct_of([("example.com", 443)], [hello]), ok)
        self.assertEqual(compat.direct_of([("example.com", 443)], [hello], ["example.com"]), ok)
        self.assertEqual(compat.direct_of([("1.2.3.4", 443)], [ip], ["1.2.3.4"]), ("https", "1.2.3.4", 443, ""))
        self.assertEqual(compat.direct_of([("1.2.3.4", 443)], [ip], [None]), ("https", "1.2.3.4", 443, ""))
        wrong = {
            (("evil.com", 443), hello, None): "evil.com (SNI: example.com)",
            (("example.com", 443), client_hello(None), None): "example.com (SNI: none)",
            (("example.com", 443), hello, ("evil.com",)): "example.com (server_hostname: ['evil.com'])",
            (("example.com", 443), hello, (None, None)): "example.com (server_hostname: [None, None])",
        }
        for (connect, data, names), host in wrong.items():
            self.assertEqual(compat.direct_of([connect], [data], names and list(names))[1], host)

    def test_http(self):
        ok = ("http", "example.com", 80, "")
        self.assertEqual(compat.direct_of([("example.com", 80)], [head("GET /x HTTP/1.1", "Host: example.com")]), ok)
        self.assertEqual(compat.direct_of([("example.com", 80)], [head("GET / HTTP/1.1", "host: example.com:80")]), ok)
        wrong = {
            head("GET / HTTP/1.1", "Host: evil.com"): "example.com (Host: evil.com)",
            head("GET / HTTP/1.1", "Host: example.com:8080"): "example.com (Host: example.com:8080)",
            head("GET / HTTP/1.1"): "example.com (no Host header)",
            head("GET http://example.com/ HTTP/1.1", "Host: example.com"):
                "example.com (request line: GET http://example.com/ HTTP/1.1)",
        }
        for data, host in wrong.items():
            self.assertEqual(compat.direct_of([("example.com", 80)], [data])[1], host)
        auth = head("GET / HTTP/1.1", "Host: example.com", "Authorization: Basic dTpw")
        self.assertEqual(compat.direct_of([("example.com", 80)], [auth]), ok[:3] + ("(Authorization header)",))
        self.assertEqual(compat.direct_of([("example.com", 443)], [head("GET / HTTP/1.1", "Host: example.com")])[0],
                         "http")  # plain HTTP where TLS was due: the scheme differs

    def test_no_single_connection(self):
        self.assertIsNone(compat.direct_of([], []))
        self.assertEqual(compat.direct_of([("example.com", 80)], [b""])[0], "no request head or ClientHello")
        self.assertEqual(compat.direct_of([("example.com", 80)] * 2, [b"", b""])[0], "several connections")
        self.assertEqual(compat.direct_of([], [b""])[0], "connections and fixture records differ")


if __name__ == "__main__":
    unittest.main()
