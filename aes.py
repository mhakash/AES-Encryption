from BitVector import *
import math
import time
import os

def ROTL8(x, shift):
  return ((x << shift) | (x >> (8-shift)))

def genSbox():
  sbox = [0] * 256

  p = 1
  q = 1

  while True:
    p = p ^ (p << 1) ^ (0x1B if (p & 0x80) > 0 else 0) 
    p &= 0xFF

    q ^= (q << 1) 
    q ^= (q << 2) 
    q ^= (q << 4) 
    q ^= (0x09 if (q & 0x80)>0 else 0)
    q &= 0xFF

    xFormed = q ^ ROTL8(q, 1) ^ ROTL8(q, 2) ^ ROTL8(q, 3) ^ ROTL8(q, 4) 
    xFormed = xFormed & 0xFF
    sbox[p] = (xFormed ^ 0x63)

    if p == 1: break

  sbox[0] = 0x63
  return sbox

Sbox = genSbox()

def genInvSbox():
  invSbox = [0]*256
  for i in range(256): invSbox[Sbox[i]] = i
  return invSbox

InvSbox = genInvSbox()

def bvH(str):
  return BitVector(hexstring=str)

Mixer = [
  [bvH("02"), bvH("03"), bvH("01"), bvH("01")],
  [bvH("01"), bvH("02"), bvH("03"), bvH("01")],
  [bvH("01"), bvH("01"), bvH("02"), bvH("03")],
  [bvH("03"), bvH("01"), bvH("01"), bvH("02")]
]

InvMixer = [
  [bvH("0E"), bvH("0B"), bvH("0D"), bvH("09")],
  [bvH("09"), bvH("0E"), bvH("0B"), bvH("0D")],
  [bvH("0D"), bvH("09"), bvH("0E"), bvH("0B")],
  [bvH("0B"), bvH("0D"), bvH("09"), bvH("0E")]
]

AES_modulus = BitVector(bitstring='100011011')

def formatKey(key, aes=128):
  word = 16
  if aes == 192: word = 24
  elif aes == 256: word = 32

  l = len(key)
  if l < word: key = key.zfill(word)
  elif l > word: key = key[-word:]
  return key

def rc(r):
  if r <= 0: return 0
  elif r == 1: return 1
  prevrc = rc(r-1)
  if prevrc < 0x80: return 2*prevrc
  else: return  (2*prevrc)^0x11B

def roundConst(r):
  b = BitVector(intVal = rc(r), size=32)
  b << 24
  return b

def g(word, r):
  w = word.deep_copy()
  
  # circular byte left shift
  w << 8
  
  # byte substitution S-Box
  x = BitVector(size = 0)
  t=0
  while t<4 :
    b = w[t*8 : (t+1)*8]
    x += BitVector(intVal = Sbox[b.intValue()], size=8)
    t += 1
  
  # add round constant
  x ^= roundConst(r)
  
  return x


def genRoundKey(*bv):
  extract = lambda x : [x[i : i+8] for i in range(0, 32, 8)]
  x = []
  for e in bv: x += extract(e) 
  roundMatrix = [0] * 4
  
  i = 0
  while i < 4: 
    roundMatrix[i] = [x[0+i], x[4+i], x[8+i], x[12+i]]
    i = i + 1
  
  return roundMatrix
  

def genRoundKeys(key, aes=128):
  keys = 11
  if aes == 192: keys = 13
  elif aes == 256: keys = 15

  r = [0] * keys;
  w = [0] * 4;

  for i in range(4):
    w[i] = BitVector(textstring = key[4*i : 4*(i+1)])

  r[0] = genRoundKey(w[0], w[1], w[2], w[3])

  n = 1
  while n < len(r):
    w[0] = w[0] ^ g(w[3], n)
    w[1] = w[1] ^ w[0]
    w[2] = w[2] ^ w[1]
    w[3] = w[3] ^ w[2]
    r[n] = genRoundKey(w[0], w[1],  w[2], w[3])
    n += 1

  return r


def mul(x,y):
  return x.gf_multiply_modular(y, AES_modulus, 8)


def mixColumns(state):
  newState = [[0 for i in range(4)] for j in range(4)] 
  for i in range(4):
    for j in range(4):
      newState[i][j] =  mul(Mixer[i][0], state[0][j]
                    ) ^ mul(Mixer[i][1], state[1][j] 
                    ) ^ mul(Mixer[i][2], state[2][j] 
                    ) ^ mul(Mixer[i][3], state[3][j] )
  return newState


def invMixColumns(state):
  newState = [[0 for i in range(4)] for j in range(4)] 
  for i in range(4):
    for j in range(4):
      newState[i][j] =  mul(InvMixer[i][0], state[0][j]
                    ) ^ mul(InvMixer[i][1], state[1][j] 
                    ) ^ mul(InvMixer[i][2], state[2][j] 
                    ) ^ mul(InvMixer[i][3], state[3][j] )
  return newState


def shiftLeft(l, n):
  return l[n:] + l[:n];


def shiftRight(r, n):
  return r[-n:] + r[:-n]


def addRoundKey(state, key):
  for i in range(4):
    for j in range(4):
      state[i][j] ^= key[i][j]
  return state


def roundMain(state, roundKey, mixCol = True):
  # substitute bytes
  for i in range(4):
    for j in range(4):
      state[i][j] = BitVector(intVal = Sbox[state[i][j].intValue()], size = 8)
  
  # shift
  for i in range(4):
    state[i] = shiftLeft(state[i], i)
  
  # mix-col
  if mixCol: state = mixColumns(state)
  
  # add round key
  state = addRoundKey(state, roundKey)
  return state


def printState(stateMatrix):
  for i in range(4):
    for j in range(4):
      print(stateMatrix[i][j].get_bitvector_in_hex(), end=' ')
    print()


def roundMainInv(state, roundKey, mixCol = True):
  # shift row
  for i in range(4):
    state[i] = shiftRight(state[i], i)

  # substitute bytes
  for i in range(4):
    for j in range(4):
      state[i][j] = BitVector(intVal = InvSbox[state[i][j].intValue()], size = 8)
  
  # add round key
  state = addRoundKey(state, roundKey)

  # mix-col
  if mixCol: state = invMixColumns(state)
  return state


def roundInit(state, roundKey):
  return addRoundKey(state, roundKey)
  

def initStateMatrix(text):
  b = lambda x : BitVector(intVal = ord(x), size=8)
  stateMatrix = [0] * 4
  i = 0
  while i < 4: 
    stateMatrix[i] = [b(text[0+i]), b(text[4+i]), b(text[8+i]), b(text[12+i])]
    i = i + 1
  return stateMatrix


def encrypt(text, roundKeys):
  rounds = len(roundKeys)
  
  stateMatrix = initStateMatrix(text)
  stateMatrix = roundInit(stateMatrix, roundKeys[0])
  for i in range(1,rounds-1):
    stateMatrix = roundMain(stateMatrix, roundKeys[i])
  stateMatrix = roundMain(stateMatrix, roundKeys[rounds-1], mixCol=False)
  
  cypherText = "";
  for i in range(4):
    for j in range(4):
      cypherText += stateMatrix[j][i].get_bitvector_in_ascii()
  
  return cypherText


def decrypt(text, roundKeys):
  rounds = len(roundKeys)
  
  stateMatrix = initStateMatrix(text)
  stateMatrix = roundInit(stateMatrix, roundKeys[rounds-1])
  for i in range(1,rounds-1):
    stateMatrix = roundMainInv(stateMatrix, roundKeys[rounds-1-i])
  stateMatrix = roundMainInv(stateMatrix, roundKeys[0], mixCol=False)

  cypherText = "";
  for i in range(4):
    for j in range(4):
      cypherText += stateMatrix[j][i].get_bitvector_in_ascii()
  return cypherText


def main():
  aes = input('which version: 1: 128, 2: 192, 3: 256 :  ')
  if aes == '2': aes = 192
  elif aes == '3': aes = 256
  else : aes = 128

  inputKey = input('Enter KEY: ')
  key = formatKey(inputKey, aes=aes)

  t0 = time.time()
  roundKeys = genRoundKeys(key, aes=aes)
  t1 = time.time()

  type = input('type( 1, 2): 1.Text 2.File: ')
  
  if type == '1':
    text = input('Enter text: ')
    chunks = math.ceil(len(text) / 16.0)
    text = text.ljust(chunks * 16);

    t2 = time.time()
    cypherText = ""
    for i in range(chunks):
      t = encrypt(text[i*16 : (i + 1)*16], roundKeys);
      cypherText += t;
    t3 = time.time()

    print('Cipher Text(in hex):\n')
    for i in cypherText: print(hex(ord(i)), end='')
    print('\n')

    t4 = time.time()
    decypher = ""
    for i in range(chunks):
      t = decrypt(cypherText[i*16 : (i + 1)*16], roundKeys);
      decypher += t
    t5 = time.time()
  
    print('decyphered text:\n', decypher)

    print('\nExecution Time')
    print('Key Scheduling:', t1-t0)
    print('Encryption time:', t3-t2)
    print('Deryption time: ', t5-t4)

  elif type=='2':
    file = input('File Name: ')
    fileName, fileExt = os.path.splitext(file)
    
    text = ''
    with open(file, 'rb') as fl:
      allBinData = fl.read()
      for x in allBinData: text+=chr(x)
    
    chunks = math.ceil(len(text) / 16.0)
    av = math.ceil(chunks/ 100.0)
    pad = chunks*16 - len(text)
    print(pad)
    for i in range(pad): text += chr(0x00)

    t2 = time.time()
    print('encryption started')
    
    cypherText = ""
    for i in range(chunks):
      t = encrypt(text[i*16 : (i + 1)*16], roundKeys);
      cypherText += t;
      if i !=0 and i%av==0: print('encryption progress: ', "{:.2f}".format(1.0*i/chunks*100), '%')
    
    print('encryption done')
    t3 = time.time()

    with open(fileName+'_encrypted'+fileExt, 'wb') as fw:
      bytesToWrite = map( lambda x: ord(x), cypherText)
      fw.write(bytes(bytesToWrite))

    t4 = time.time()
    print('decryption started')
    decypher = ""
    for i in range(chunks):
      t = decrypt(cypherText[i*16 : (i + 1)*16], roundKeys);
      decypher += t
      if i!= 0 and i%av==0 : print('decryption progress: ',"{:.2f}".format(1.0*i/chunks*100), '%')
    t5 = time.time()
    
    print('decryption done')
    print('\nExecution Time')
    print('Key Scheduling:', t1-t0)
    print('Encryption time: ', t3-t2)
    print('Deryption time: ', t5-t4)

    with open(fileName+'_decrypted'+fileExt, 'wb') as fw:
      bytesToWrite = map( lambda x: ord(x), decypher)
      fw.write(bytes(bytesToWrite))
  else:
    print('Invalid Input')


if __name__ == "__main__":
  main()