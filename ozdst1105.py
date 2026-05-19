"""
O'z DSt 1105:2009  —  Алгоритм шифрування даних (АШД)
Державний стандарт Узбекистану: симетричний блоковий шифр

====================================================================
  Параметри (§6.1)
====================================================================
  Блок              : 256 біт  (32 байти)
  Ключ k            : 256 або 512 біт
  Функціональний kf : 256 біт
  Кількість раундів : e = 8
  Модуль            : p = 256

====================================================================
  Алгебраїчні примітки (доведено аналізом контрольного прикладу)
====================================================================
  Kse обчислюється як k + k'·(1 + kf·k) у цілочисельній арифметиці,
    береться 672 старших бітів (§6.3.1.1).
  Kst = kse[44:76]  (ліві 256 біт правих 320 біт Kse, §6.3.1.2).
  Діаматриця K будується за схемою §6.3.2.2:
      діагональ = kss[6],  d8 = kss[3],  d9 = kss[4]  тощо.
  Ensure_invertible забезпечує непарність (непарність) всіх чотирьох
    множників діавизначника (§5.1.4), що гарантує оборотність mod 256.
  Aralash виконує ⊗₂ (§5.1.5) суворо mod 256.
    Зворотна операція реалізована через 16×16 лінійне обернення mod 256.
  Масиви замін BsA обчислюються через pow(x, d, 257) % 256 (§6.3.1.4).
  Epoch-ключі — ліві 256 бітів циклічно зсуненого Kse (§6.3.5).
"""

from __future__ import annotations
from typing import List, Tuple, Optional

# ====================================================================
# Константи
# ====================================================================
BLOCK  = 32         # байти (256 біт)
ROWS   = 8          # рядки Holat
COLS   = 4          # стовпці Holat
ROUNDS = 8          # раундів e
P      = 256        # арифметика mod p
KSE_B  = 84         # Kse у байтах (672 біт)
KSE_N  = 672        # Kse у бітах
STEP   = 83         # зсув між epoch-ключами (бітів)

H4 = List[List[int]]   # матриця 4×4
H8 = List[List[int]]   # масив  8×4


# ====================================================================
# Holat I/O
# ====================================================================

def _to_holat(data: bytes) -> H8:
    """Завантаження 32-байт блоку у Holat[8][4] рядково (4 байти/рядок)."""
    assert len(data) == BLOCK
    return [[data[r * COLS + c] for c in range(COLS)] for r in range(ROWS)]


def _from_holat(h: H8) -> bytes:
    """Вивантаження Holat[8][4] у 32 байти."""
    return bytes(h[r][c] & 0xFF for r in range(ROWS) for c in range(COLS))


def _xor(a: H8, b: H8) -> H8:
    """Qo'shHolat / Qo'shBosqichKalit: побітовий XOR (§6.3.6, §6.3.8)."""
    return [[(a[r][c] ^ b[r][c]) & 0xFF for c in range(COLS)] for r in range(ROWS)]


# ====================================================================
# §6.3.1  Kse + масиви замін
# ====================================================================

def _compute_kse(k: bytes, kf: bytes) -> bytes:
    """
    §6.3.1.1  kse = k + k'·(1 + kf·k)  у цілочисельній арифметиці.
    k' = праві 192 біти kf.  Повертає ліві 672 біти.
    """
    k_i  = int.from_bytes(k, 'big')
    kf_i = int.from_bytes(kf, 'big')
    kp_i = int.from_bytes(kf[8:], 'big')   # останні 24 байти kf
    v    = k_i + kp_i * (1 + kf_i * k_i)
    bl   = v.bit_length()
    top  = v >> (bl - KSE_N) if bl >= KSE_N else v << (KSE_N - bl)
    return top.to_bytes(KSE_B, 'big')


def _bsa(d: int, R: int, L: int, b_swap: int) -> List[int]:
    """§6.3.1.4  Масив замін BsA[256] через pow(x, d, 257) % 256."""
    arr = [pow(((i + L) % 256) + 1, d, 257) % 256 for i in range(256)]
    b = b_swap
    for i in range(1, 256):
        if not ((i - arr[i]) % 256 != 0 and abs(arr[i - 1] - arr[i]) >= 8):
            addr = (i - b) % 256
            arr[i], arr[addr] = arr[addr], arr[i]
            b = (b - 5) % 256
    return arr


def _fix_d(d: int) -> int:
    """§6.3.1.3 п.4–5: корекція парного степеня."""
    if d % 2 == 0:
        d = d - 1 if d % 4 == 0 else d + 1
    if d % 2 == 1 and (d - 1) % 4 == 0:
        d -= 2
    return max(d, 3)


def shakl_seans_kalit_bayt(
    k: bytes, kf: bytes
) -> Tuple[List[int], List[int], List[int], List[int], bytes]:
    """
    §6.3.1  Обчислює Kse, Kst, масиви BsA.
    Повертає (B1A, B2A, B1AD, B2AD, kst_bytes).
    """
    kse = _compute_kse(k, kf)

    # §6.3.1.2: права 320-бітна частина Kse → Kst (32 б) + B (8 б)
    kst = kse[KSE_B - 40 : KSE_B - 8]
    B   = list(kse[KSE_B - 8 :])

    def param(j_val, j_zero=1):
        return j_val if j_val else j_zero

    d1 = _fix_d(B[0] if B[0] >= 3 else 3)
    R1 = param(B[1]); L1 = param(B[2]); b3 = param(B[3])
    d2 = _fix_d(B[4] if B[4] >= 3 else 3)
    R2 = param(B[5]); L2 = param(B[6]); b7 = param(B[7])

    B1A  = _bsa(d1, R1, L1, b3)
    B2A  = _bsa(d2, R2, L2, b7)
    B1AD = [0] * 256
    for i, v in enumerate(B1A): B1AD[v & 0xFF] = i
    B2AD = [0] * 256
    for i, v in enumerate(B2A): B2AD[v & 0xFF] = i

    return B1A, B2A, B1AD, B2AD, kst


# ====================================================================
# §6.3.2  Сеансовий ключ: діаматриці K1, K2
# ====================================================================

def _build_dm(kss: List[int]) -> H4:
    """
    §6.3.2.2  Діаматриця 4×4 зі спеціальною структурою.
    Відображення kss → d:  kss[6] = d7 (діагональ),
    kss[3] = d8, kss[4] = d9, kss[5] = d3, kss[7] = d4,
    kss[8] = d5, kss[9] = d6, kss[0..2] = d0..d2.

    Матриця:
        d7  d0  d1  d2       kss[6]  kss[0]  kss[1]  kss[2]
        d8  d7  d8  d8  =   kss[3]  kss[6]  kss[3]  kss[3]
        d9  d3  d7  d9       kss[4]  kss[5]  kss[6]  kss[4]
        d4  d5  d6  d7       kss[7]  kss[8]  kss[9]  kss[6]
    """
    return [
        [kss[6], kss[0], kss[1], kss[2]],
        [kss[3], kss[6], kss[3], kss[3]],
        [kss[4], kss[5], kss[6], kss[4]],
        [kss[7], kss[8], kss[9], kss[6]],
    ]


def _ensure_inv(kss: List[int]) -> List[int]:
    """
    §6.3.2.1  Гарантує непарність всіх множників діавизначника mod 2,
    що забезпечує оборотність ⊗₂ mod 256.

    Множники (для K1):
      d7          = kss[6]
      f1 = d7+d0+d8+d3+d5 = kss[6]+kss[0]+kss[3]+kss[5]+kss[8]
      f2 = d7+d1+d8+d9+d6 = kss[6]+kss[1]+kss[3]+kss[4]+kss[9]
      f3 = d7+d2+d8+d9+d4 = kss[6]+kss[2]+kss[3]+kss[4]+kss[7]
    """
    kss = kss[:]
    for i in range(20):
        if kss[i] == 0:
            kss[i] = (kss[i] - 1) % P

    # Діагональний елемент d7 має бути непарним
    if kss[6]  % 2 == 0: kss[6]  = (kss[6]  - 1) % P
    if kss[16] % 2 == 0: kss[16] = (kss[16] - 1) % P

    # Кожен множник fi має бути непарним
    # K1 factors:                     K2 factors (зсув +10):
    for diag, others, target in [
        (6,  [0, 3, 5, 8],  8),      # f1 K1  → fix kss[8]
        (16, [10,13,15,18], 18),     # f1 K2  → fix kss[18]
        (6,  [1, 3, 4, 9],  9),      # f2 K1  → fix kss[9]
        (16, [11,13,14,19], 19),     # f2 K2  → fix kss[19]
        (6,  [2, 3, 4, 7],  7),      # f3 K1  → fix kss[7]
        (16, [12,13,14,17], 17),     # f3 K2  → fix kss[17]
    ]:
        if (kss[diag] + sum(kss[o] for o in others)) % 2 == 0:
            kss[target] = (kss[target] - 1) % P

    return kss


def _build_linmap(K: H4) -> List[List[int]]:
    """Будує 16×16 лінійне відображення для ⊗₂ з фіксованим K mod 256."""
    A = [[0] * 16 for _ in range(16)]
    for i in range(16):
        e = [[1 if r * 4 + c == i else 0 for c in range(4)] for r in range(4)]
        res = _diamatrix(e, K)
        for r in range(4):
            for c in range(4):
                A[r * 4 + c][i] = res[r][c]
    return A


def _invert_linmap(A: List[List[int]]) -> Optional[List[List[int]]]:
    """Обернення 16×16 матриці mod 256 методом Гаусса–Жордана (зведена форма)."""
    n = len(A)
    aug = [A[i][:] + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for col in range(n):
        piv = next((r for r in range(col, n) if aug[r][col] % 2 == 1), None)
        if piv is None:
            return None   # не оборотна
        aug[col], aug[piv] = aug[piv], aug[col]
        inv_p = pow(int(aug[col][col]), -1, 256)
        aug[col] = [(v * inv_p) % 256 for v in aug[col]]
        for row in range(n):
            if row != col and aug[row][col] % 256:
                f = aug[row][col]
                aug[row] = [(aug[row][j] - f * aug[col][j]) % 256
                            for j in range(2 * n)]
    return [[aug[i][n + j] % 256 for j in range(n)] for i in range(n)]


def shakl_seans_kalit(kst: bytes) -> Tuple[H4, H4, List[List[int]], List[List[int]]]:
    """
    §6.3.2  Будує K1, K2 та їх обернені лінійні відображення mod 256.
    Повертає (K1, K2, A1_inv, A2_inv).
    """
    kss  = _ensure_inv(list(kst[:20]))
    K1   = _build_dm(kss[:10])
    K2   = _build_dm(kss[10:20])
    A1   = _build_linmap(K1)
    A2   = _build_linmap(K2)
    A1i  = _invert_linmap(A1)
    A2i  = _invert_linmap(A2)
    if A1i is None or A2i is None:
        raise ValueError("Діаматриця не оборотна mod 256 — перевірте kst")
    return K1, K2, A1i, A2i


# ====================================================================
# §5.1.5 / §6.3.3  Aralash: операція ⊗₂ та її обернення
# ====================================================================

def _diamatrix(H: H4, K: H4) -> H4:
    """
    §5.1.5  Діаматричне множення H ⊗₂ K (mod 256).

    Діагональні:
      h'[u,u] = h[u,u]·Σ_i k[i,u] − Σ_{i≠u} h[i,i]·k[i,u]
    Позадіагональні:
      h'[s,u] = h[s,u]·Σ_i k[i,u] + k[s,u]·Σ_i h[i,u] − Σ_{i≠s,u} h[s,i]·k[i,u]
    """
    n = 4
    Hp = [[0] * n for _ in range(n)]
    cs  = [sum(K[i][u] for i in range(n)) % P for u in range(n)]
    hcs = [sum(H[i][u] for i in range(n)) % P for u in range(n)]

    for u in range(n):
        Hp[u][u] = (H[u][u] * cs[u]
                    - sum(H[i][i] * K[i][u] for i in range(n) if i != u)) % P

    for s in range(n):
        for u in range(n):
            if s == u:
                continue
            cross = sum(H[s][i] * K[i][u] for i in range(n) if i != s and i != u)
            Hp[s][u] = (H[s][u] * cs[u] + K[s][u] * hcs[u] - cross) % P

    return Hp


def _apply_inv(Ai: List[List[int]], H: H4) -> H4:
    """Застосовує обернене лінійне відображення 16×16 до матриці 4×4."""
    hf = [H[r][c] for r in range(4) for c in range(4)]
    rf = [sum(Ai[i][j] * hf[j] for j in range(16)) % P for i in range(16)]
    return [[rf[r * 4 + c] for c in range(4)] for r in range(4)]


def aralash(h: H8, K1: H4, K2: H4) -> H8:
    """
    §6.3.3  Шифрування: ліва половина Holat (рядки 0–3) ⊗₂ K1,
                         права (рядки 4–7) ⊗₂ K2.
    """
    return (_diamatrix([h[r][:] for r in range(4)], K1)
            + _diamatrix([h[r][:] for r in range(4, 8)], K2))


def aralash_inv(h: H8, A1i: List[List[int]], A2i: List[List[int]]) -> H8:
    """Розшифрування: застосовує обернені лінійні відображення до обох половин."""
    return (_apply_inv(A1i, [h[r][:] for r in range(4)])
            + _apply_inv(A2i, [h[r][:] for r in range(4, 8)]))


# ====================================================================
# §6.3.4  BaytAlmash: побайтова заміна
# ====================================================================

def bayt_almash(h: H8, Ba: List[int]) -> H8:
    """§6.3.4  Заміна h[r][c] → Ba[h[r][c]]."""
    return [[Ba[h[r][c]] & 0xFF for c in range(COLS)] for r in range(ROWS)]


# ====================================================================
# §6.3.7  Sur: циклічні зсуви
# ====================================================================

def sur_enc(h: H8) -> H8:
    """
    §6.3.7 (шифрування):
    1. Стовпець j ↓ на (j+1) mod 8 позицій.
    2. Рядок i → на (i+1) mod 4 позиції.
    """
    h1 = [[0] * COLS for _ in range(ROWS)]
    for col in range(COLS):
        s = (col + 1) % ROWS
        for row in range(ROWS):
            h1[(row + s) % ROWS][col] = h[row][col]
    h2 = [[0] * COLS for _ in range(ROWS)]
    for row in range(ROWS):
        s = (row + 1) % COLS
        for col in range(COLS):
            h2[row][(col + s) % COLS] = h1[row][col]
    return h2


def sur_dec(h: H8) -> H8:
    """
    §6.3.7 (розшифрування):
    1. Рядок i ← на (i+1) mod 4 позиції.
    2. Стовпець j ↑ на (j+1) mod 8 позицій.
    """
    h1 = [[0] * COLS for _ in range(ROWS)]
    for row in range(ROWS):
        s = (row + 1) % COLS
        for col in range(COLS):
            h1[row][col] = h[row][(col + s) % COLS]
    h2 = [[0] * COLS for _ in range(ROWS)]
    for col in range(COLS):
        s = (col + 1) % ROWS
        for row in range(ROWS):
            h2[row][col] = h1[(row + s) % ROWS][col]
    return h2


# ====================================================================
# §6.3.5  Epoch-ключі
# ====================================================================

def _rot_left(v: int, s: int, b: int) -> int:
    s %= b
    m = (1 << b) - 1
    return ((v << s) | (v >> (b - s))) & m


def _rot_right(v: int, s: int, b: int) -> int:
    return _rot_left(v, b - s % b, b)


def build_epoch_keys(kse: bytes, encrypt: bool) -> List[H8]:
    """
    §6.3.5  Формує ROUNDS+1 масивів Ke[8][4].
    Для розшифрування: початковий зсув + зворотні зсуви між раундами.
    """
    cur = int.from_bytes(kse, 'big') & ((1 << KSE_N) - 1)
    if not encrypt:
        init = (KSE_N - (ROUNDS * STEP) % KSE_N) % KSE_N
        cur  = _rot_left(cur, init, KSE_N)

    keys: List[H8] = []
    for step in range(ROUNDS + 1):
        if step > 0:
            cur = (_rot_left(cur, STEP, KSE_N) if encrypt
                   else _rot_right(cur, STEP, KSE_N))
        ke_int = (cur >> (KSE_N - 8 * BLOCK)) & ((1 << (8 * BLOCK)) - 1)
        keys.append(_to_holat(ke_int.to_bytes(BLOCK, 'big')))
    return keys


# ====================================================================
# §6.2  Шифрування / розшифрування блоку
# ====================================================================

def _enc_block(
    pt: bytes,
    K1: H4, K2: H4,
    enc_keys: List[H8],
    B1A: List[int], B2A: List[int],
) -> bytes:
    """
    §6.2  Рис. 7  ECB-шифрування одного блоку.
    e раундів: XOR_key → Aralash → Sur → BaytAlmash
    Фінал:     XOR_key → Aralash
    """
    h = _to_holat(pt)
    for step in range(ROUNDS):
        h = _xor(h, enc_keys[step])
        h = aralash(h, K1, K2)
        h = sur_enc(h)
        h = bayt_almash(h, B1A if (step + 1) % 2 == 1 else B2A)
    h = _xor(h, enc_keys[ROUNDS])
    h = aralash(h, K1, K2)
    return _from_holat(h)


def _dec_block(
    ct: bytes,
    A1i: List[List[int]], A2i: List[List[int]],
    enc_keys: List[H8],
    B1AD: List[int], B2AD: List[int],
) -> bytes:
    """
    §6.3  Рис. 7  ECB-розшифрування одного блоку.
    Початок:  Aralash⁻¹ → XOR_key[ROUNDS]
    e раундів (зворотньо): BaytAlmash⁻¹ → Sur⁻¹ → Aralash⁻¹ → XOR_key
    """
    h = _to_holat(ct)
    h = aralash_inv(h, A1i, A2i)
    h = _xor(h, enc_keys[ROUNDS])
    for step in range(ROUNDS, 0, -1):
        h = bayt_almash(h, B1AD if step % 2 == 1 else B2AD)
        h = sur_dec(h)
        h = aralash_inv(h, A1i, A2i)
        h = _xor(h, enc_keys[step - 1])
    return _from_holat(h)


# ====================================================================
# Публічний API
# ====================================================================

class ASD:
    """
    O'z DSt 1105:2009 — Алгоритм шифрування даних.

    Симетричний блоковий шифр: блок 256 біт.

    Режими:
      ECB  (Elektron kod kitobi)         — незалежні блоки
      CBC  (ShifrBloklarni ilaktirish)   — зчеплення блоків з IV

    Приклад (ECB):
        cipher = ASD(k_32b, kf_32b)
        ct = cipher.encrypt_ecb(cipher.pad(plaintext))
        pt = cipher.unpad(cipher.decrypt_ecb(ct))

    Приклад (CBC):
        ct = cipher.encrypt_cbc(cipher.pad(plaintext), iv_32b)
        pt = cipher.unpad(cipher.decrypt_cbc(ct, iv_32b))

    Параметри __init__:
        k   — 32 або 64 байти.  Якщо 64: перші 32 = k, останні 32 = kf.
        kf  — 32 байти (необов'язково; якщо None — генерується з k).
    """

    def __init__(self, k: bytes, kf: Optional[bytes] = None):
        if len(k) == 64:
            kf, k = k[32:], k[:32]
        elif len(k) != 32:
            raise ValueError("k має бути 32 або 64 байти")
        if kf is None:
            kf = bytes((k[i] ^ k[(i + 7) % 32] ^ (i * 37 + 19)) & 0xFF
                       for i in range(32))
        if len(kf) != 32:
            raise ValueError("kf має бути 32 байти")

        self.k, self.kf = k, kf
        self._init()

    # === Ініціалізація ====================================================

    def _init(self) -> None:
        B1A, B2A, B1AD, B2AD, kst = shakl_seans_kalit_bayt(self.k, self.kf)
        self._B1A  = B1A;  self._B2A  = B2A
        self._B1AD = B1AD; self._B2AD = B2AD

        self._K1, self._K2, self._A1i, self._A2i = shakl_seans_kalit(kst)

        kse = _compute_kse(self.k, self.kf)
        self._enc_keys = build_epoch_keys(kse, encrypt=True)
        # Decrypt використовує enc_keys в REVERSE ORDER

    # === ECB ==============================================================

    def encrypt_ecb(self, data: bytes) -> bytes:
        """ECB-шифрування. len(data) кратне 32."""
        _chk(data)
        return b"".join(
            _enc_block(data[i:i+BLOCK], self._K1, self._K2,
                       self._enc_keys, self._B1A, self._B2A)
            for i in range(0, len(data), BLOCK)
        )

    def decrypt_ecb(self, data: bytes) -> bytes:
        """ECB-розшифрування."""
        _chk(data)
        return b"".join(
            _dec_block(data[i:i+BLOCK], self._A1i, self._A2i,
                       self._enc_keys, self._B1AD, self._B2AD)
            for i in range(0, len(data), BLOCK)
        )

    # === CBC ==================================================================

    def encrypt_cbc(self, data: bytes, iv: bytes) -> bytes:
        """CBC-шифрування."""
        _chk(data); _chk_iv(iv)
        out = bytearray()
        prev = _to_holat(iv)
        for i in range(0, len(data), BLOCK):
            blk  = _xor(_to_holat(data[i:i+BLOCK]), prev)
            ctb  = _enc_block(_from_holat(blk), self._K1, self._K2,
                               self._enc_keys, self._B1A, self._B2A)
            out += ctb
            prev = _to_holat(ctb)
        return bytes(out)

    def decrypt_cbc(self, data: bytes, iv: bytes) -> bytes:
        """CBC-розшифрування."""
        _chk(data); _chk_iv(iv)
        out    = bytearray()
        prev   = iv
        for i in range(0, len(data), BLOCK):
            ct_b = data[i:i+BLOCK]
            pt_b = _dec_block(ct_b, self._A1i, self._A2i,
                               self._enc_keys, self._B1AD, self._B2AD)
            pt_h = _xor(_to_holat(pt_b), _to_holat(prev))
            out += _from_holat(pt_h)
            prev = ct_b
        return bytes(out)

    # === Вирівнювання ==========================================================

    def pad(self, data: bytes) -> bytes:
        """Додає PKCS#7-сумісне вирівнювання до кратності 32."""
        n = BLOCK - len(data) % BLOCK
        return data + bytes([n] * n)

    def unpad(self, data: bytes) -> bytes:
        """Видаляє вирівнювання."""
        if not data:
            return data
        n = data[-1]
        if n == 0 or n > BLOCK:
            raise ValueError("Некоректне вирівнювання")
        return data[:-n]


# ====================================================================
# Внутрішні перевірки
# ====================================================================

def _chk(data: bytes) -> None:
    if len(data) % BLOCK:
        raise ValueError(f"Довжина {len(data)} не кратна {BLOCK}. "
                         "Використайте cipher.pad(data).")

def _chk_iv(iv: bytes) -> None:
    if len(iv) != BLOCK:
        raise ValueError(f"IV має бути {BLOCK} байтів")

def demo() -> None:
    print("=" * 68)
    print("  O'z DSt 1105:2009 — Алгоритм шифрування даних (АШД)")
    print("  Симетричний блоковий шифр  |  блок 256 біт  |  e = 8 раундів")
    print("=" * 68)

    k  = bytes.fromhex("37B60BBA0AB160CFDC18F50CDEE8E04530B3F8AF"
                       "1432FE511FBB2029112F2143")
    kf = bytes.fromhex("47E7694669C546B6FE163A89B0D896D6238B2315"
                       "32C404349CB0C7AA813DF96D")
    iv = bytes.fromhex("2654BB5FA375D89854EA489F9AA88416"
                       "FD4DEBBD9B3B403348F29FEE5234C37A")

    cipher = ASD(k, kf)
    msg    = b"Confidential data protected by O'z DSt 1105:2009!"
    padded = cipher.pad(msg)

    print(f"\nПовідомлення : {msg.decode()}")
    print(f"Розмір (байт): {len(padded)}")

    ct = cipher.encrypt_ecb(padded)
    rt = cipher.unpad(cipher.decrypt_ecb(ct))
    print(f"\n[ECB] CT : {ct.hex().upper()}")
    print(f"[ECB] PT : {rt.decode()}")
    print(f"[ECB]    : {'OK' if rt == msg else 'ПОМИЛКА'}")

    ct2 = cipher.encrypt_cbc(padded, iv)
    rt2 = cipher.unpad(cipher.decrypt_cbc(ct2, iv))
    print(f"\n[CBC] CT : {ct2.hex().upper()}")
    print(f"[CBC] PT : {rt2.decode()}")
    print(f"[CBC]    : {'OK' if rt2 == msg else 'ПОМИЛКА'}")

if __name__ == "__main__":
    demo()
