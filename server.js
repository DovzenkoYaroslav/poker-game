const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: { origin: '*', methods: ['GET', 'POST'] }
});

// Константы
const MAX_ROOMS = 100;
const MAX_PLAYERS_PER_ROOM = 10;
const ROOM_TTL = 24 * 60 * 60 * 1000; // 24 часа
const SB_AMOUNT = 20;
const BB_AMOUNT = 40;
const TURN_TIME = 30000;
const START_GAME_DELAY = 10000; // 10 секунд перед стартом

// Простая "БД" в JSON-файле
const DB_PATH = path.join(__dirname, 'rooms.json');
let roomsFromFile = {};

try {
  if (fs.existsSync(DB_PATH)) {
    const raw = fs.readFileSync(DB_PATH, 'utf8');
    roomsFromFile = JSON.parse(raw);
  }
} catch (e) {
  console.error('Ошибка чтения rooms.json:', e);
  roomsFromFile = {};
}

// Атомарное сохранение через временный файл
function saveRoomsToFile() {
  try {
    const tmpPath = DB_PATH + '.tmp';
    fs.writeFileSync(tmpPath, JSON.stringify(roomsFromFile, null, 2));
    fs.renameSync(tmpPath, DB_PATH);
  } catch (e) {
    console.error('Ошибка сохранения rooms.json:', e);
  }
}

// Глобальная статистика по никам (сохраняется между сессиями)
const STATS_PATH = path.join(__dirname, 'stats_data.json');
let globalStats = {};

try {
  if (fs.existsSync(STATS_PATH)) {
    globalStats = JSON.parse(fs.readFileSync(STATS_PATH, 'utf8'));
  }
} catch (e) {
  console.error('Ошибка чтения stats_data.json:', e);
  globalStats = {};
}

function saveGlobalStats() {
  try {
    const tmpPath = STATS_PATH + '.tmp';
    fs.writeFileSync(tmpPath, JSON.stringify(globalStats, null, 2));
    fs.renameSync(tmpPath, STATS_PATH);
  } catch (e) {
    console.error('Ошибка сохранения stats_data.json:', e);
  }
}

function syncPlayerToGlobal(player) {
  if (!player || player.isBot || !player.name) return;
  const key = player.name.toLowerCase();
  const s = player.stats || {};
  const existing = globalStats[key] || { handsPlayed: 0, wins: 0, maxWin: 0, maxBet: 0, actions: 0, stack: 1000 };
  globalStats[key] = {
    handsPlayed: Math.max(existing.handsPlayed, s.handsPlayed || 0),
    wins: Math.max(existing.wins, s.wins || 0),
    maxWin: Math.max(existing.maxWin, s.maxWin || 0),
    maxBet: Math.max(existing.maxBet, s.maxBet || 0),
    actions: Math.max(existing.actions, s.actions || 0),
    stack: Math.max(existing.stack, player.stack || 0)
  };
}

app.use(express.static(path.join(__dirname, 'public')));
app.get('/', (req, res) => {
  res.sendFile(path.join(__dirname, 'public', 'index.html'));
});

// --- ИГРОВОЙ ДВИЖОК ---

const SUITS = ['♠', '♥', '♦', '♣'];
const RANKS = ['2', '3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K', 'A'];
const HAND_RANKS = {
  HIGH_CARD: 0, ONE_PAIR: 1, TWO_PAIR: 2, THREE_OF_A_KIND: 3,
  STRAIGHT: 4, FLUSH: 5, FULL_HOUSE: 6, FOUR_OF_A_KIND: 7,
  STRAIGHT_FLUSH: 8, ROYAL_FLUSH: 9
};

const BOT_NAMES = ['Бот Алекс', 'Бот Джесс', 'Бот Крис'];

// ---------- ВАЛИДАЦИЯ ----------
function validatePlayerName(name) {
  if (typeof name !== 'string') return false;
  const trimmed = name.trim();
  return trimmed.length >= 1 && trimmed.length <= 20 && /^[а-яА-ЯёЁa-zA-Z0-9_\- ]+$/.test(trimmed);
}

function validateRoomId(roomId) {
  return typeof roomId === 'string' && /^[A-Z0-9]{6}$/.test(roomId);
}

function validateAction(action, amount, player, gameState) {
  if (!['fold', 'check', 'call', 'raise', 'allin'].includes(action)) return false;
  
  const currentBet = gameState.currentBet;
  const playerBet = player.currentBet || 0;

  if (action === 'call' && playerBet >= currentBet) return false;
  if (action === 'check' && playerBet < currentBet) return false;
  
  if (action === 'raise') {
    if (typeof amount !== 'number' || amount <= 0) return false;
    
    const minRaise = gameState.minRaise || currentBet * 2;
    const toCall = currentBet - playerBet;
    const totalNeeded = Math.max(minRaise, toCall + (gameState.lastRaiseSize || 0));
    
    if (amount < totalNeeded && amount < (player.stack || 0) + playerBet) return false;
    if (amount > (player.stack || 0) + playerBet) return false;
  }
  
  return true;
}

function sanitizeHtml(str) {
  return String(str)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;');
}

// ---------- ПОЗИЦИИ ----------
function assignPositions(players, dealerIndex) {
  const n = players.length;
  const positions = new Array(n);
  const extra = ['EP', 'MP', 'HJ', 'CO'];
  
  if (n === 2) {
    positions[dealerIndex] = 'SB';
    positions[(dealerIndex + 1) % n] = 'BB';
    return positions;
  }
  
  positions[dealerIndex] = 'BTN';
  positions[(dealerIndex + 1) % n] = 'SB';
  positions[(dealerIndex + 2) % n] = 'BB';
  
  let extraIdx = 3;
  let extraPosIdx = 0;
  while (extraIdx < n) {
    positions[(dealerIndex + extraIdx) % n] = extra[extraPosIdx % extra.length];
    extraIdx++;
    extraPosIdx++;
  }
  return positions;
}

// --- Управление комнатами ---
const rooms = new Map();
const socketToRoom = new Map();

function loadRooms() {
  const now = Date.now();
  for (const [roomId, roomData] of Object.entries(roomsFromFile)) {
    try {
      const lastActivity = roomData.lastActivity || 0;
      if (roomData.players?.length === 0 || now - lastActivity > ROOM_TTL) {
        delete roomsFromFile[roomId];
        continue;
      }
      
      const room = { ...roomData, gameState: null, turnTimer: null, startTimer: null };
      room.players = room.players.map(p => ({
        ...p, cards: [], connected: false, currentBet: 0, hasActed: false,
        stats: p.stats || { handsPlayed: 0, wins: 0, maxWin: 0, maxBet: 0, actions: 0 }
      }));
      rooms.set(roomId, room);
    } catch(e) {}
  }
  saveRoomsToFile();
}
loadRooms();

setInterval(() => {
  const now = Date.now();
  for (const [roomId, room] of rooms) {
    if (room.players.every(p => !p.connected) || now - (room.lastActivity || 0) > ROOM_TTL) {
      if (room.startTimer) clearTimeout(room.startTimer);
      if (room.turnTimer) clearTimeout(room.turnTimer);
      rooms.delete(roomId);
      delete roomsFromFile[roomId];
    }
  }
  saveRoomsToFile();
}, 30 * 60 * 1000);

function saveRoom(roomId) {
  const room = rooms.get(roomId);
  if (!room) return;
  
  const toSave = {
    id: room.id,
    players: room.players
      .filter(p => !p.isBot)
      .map(p => ({ 
        id: p.id, 
        name: p.name, 
        stack: p.stack, 
        isAdmin: p.isAdmin, 
        seat: p.seat,
        stats: p.stats 
      })),
    creator: room.creator,
    lastActivity: room.lastActivity || Date.now()
  };
  roomsFromFile[roomId] = toSave;
  room.players.forEach(syncPlayerToGlobal);
  saveGlobalStats();
  saveRoomsToFile();
}

function generateRoomId() {
  const bytes = crypto.randomBytes(4);
  return bytes.toString('hex').toUpperCase().slice(0, 6);
}

function findAvailableSeat(room) {
  const taken = new Set(room.players.filter(p => !p.isBot).map(p => p.seat));
  for (let i = 0; i < MAX_PLAYERS_PER_ROOM; i++) {
    if (!taken.has(i)) return i;
  }
  return -1;
}

// ---- Таймер хода ----
function startTurnTimer(room) {
  if (room.turnTimer) clearTimeout(room.turnTimer);
  const gs = room.gameState;
  if (!gs || gs.stage === 'showdown') return;
  const handPlayers = room._handPlayers || room.players;
  const currentPlayer = handPlayers[gs.currentPlayerIndex];
  if (!currentPlayer || currentPlayer.isBot) return;

  gs.turnDeadline = Date.now() + TURN_TIME;
  updateRoomState(room.id);
  room.turnTimer = setTimeout(() => {
    if (gs !== room.gameState) return;
    const player = handPlayers[gs.currentPlayerIndex];
    if (player && !player.hasActed && gs.stage !== 'showdown') {
      const action = player.currentBet === gs.currentBet ? 'check' : 'fold';
      processAction(room, player, action);
    }
  }, TURN_TIME);
}

// ---- 10-секундный отсчёт перед стартом игры ----
function startGameCountdown(room) {
  if (room.startTimer) clearTimeout(room.startTimer);
  let remaining = START_GAME_DELAY / 1000;
  
  room.startTimer = setInterval(() => {
    remaining--;
    room.players.forEach(p => {
      if (!p.isBot) {
        io.to(p.id).emit('gameStarting', { remaining });
      }
    });
    
    if (remaining <= 0) {
      clearInterval(room.startTimer);
      room.startTimer = null;
      startNewHand(room);
    }
  }, 1000);
}

// ---- Логика бота ----
function botAction(room) {
  const gs = room.gameState;
  if (!gs || gs.stage === 'showdown' || gs.stage === 'waiting') return;
  const handPlayers = room._handPlayers || room.players;
  const currentPlayer = handPlayers[gs.currentPlayerIndex];
  if (!currentPlayer || !currentPlayer.isBot) return;

  const rand = Math.random();
  let action = 'call';
  let amount = 0;
  const currentBet = gs.currentBet;
  const toCall = currentBet - currentPlayer.currentBet;

  if (toCall === 0) {
    if (rand < 0.15) {
      action = 'raise';
      amount = gs.minRaise || currentBet * 2;
    } else {
      action = 'check';
    }
  } else {
    if (rand < 0.2) {
      action = 'fold';
    } else if (rand < 0.35 && currentPlayer.stack > toCall) {
      const minRaise = gs.minRaise || currentBet * 2;
      const raiseNeeded = minRaise - currentPlayer.currentBet;
      if (raiseNeeded <= currentPlayer.stack) {
        action = 'raise';
        amount = minRaise;
      } else {
        action = 'call';
      }
    } else {
      action = 'call';
    }
  }

  processAction(room, currentPlayer, action, amount);
}

// ---- Игровые действия ----
function processAction(room, player, action, amount) {
  const gs = room.gameState;
  const currentBet = gs.currentBet;

  if (!player.stats) player.stats = { handsPlayed: 0, wins: 0, maxWin: 0, maxBet: 0, actions: 0 };
  player.stats.actions++;
  if (!player.handMaxBet) player.handMaxBet = 0;
  if (player.totalBet === undefined) player.totalBet = 0;

  let actionSucceeded = false;

  switch (action) {
    case 'fold':
      player.cards = [];
      actionSucceeded = true;
      break;
    case 'check':
      if (player.currentBet >= currentBet) {
        actionSucceeded = true;
      }
      break;
    case 'call':
      let callAmount = currentBet - player.currentBet;
      if (callAmount > player.stack) callAmount = player.stack;
      if (callAmount > 0) {
        player.stack -= callAmount;
        player.totalBet += callAmount;
        player.currentBet += callAmount;
      }
      actionSucceeded = true;
      break;
    case 'allin':
      const allIn = player.stack;
      if (allIn <= 0) break;
      player.stack -= allIn;
      player.totalBet += allIn;
      player.currentBet += allIn;
      if (player.currentBet > gs.currentBet) {
        gs.currentBet = player.currentBet;
        gs.lastRaiseIndex = (room._handPlayers || room.players).indexOf(player);
        (room._handPlayers || room.players).forEach(p => {
          if (p !== player && p.cards && p.cards.length > 0) p.hasActed = false;
        });
      }
      actionSucceeded = true;
      break;
    case 'raise':
      const minRaiseAmt = gs.minRaise || currentBet * 2;
      let raiseAmount = amount || minRaiseAmt;
      if (raiseAmount < minRaiseAmt) raiseAmount = minRaiseAmt;
      const needed = raiseAmount - player.currentBet;
      const actualRaise = Math.min(needed, player.stack);
      if (actualRaise <= 0) break;
      const previousBet = gs.currentBet;
      player.stack -= actualRaise;
      player.totalBet += actualRaise;
      player.currentBet += actualRaise;
      if (player.currentBet > gs.currentBet) {
        gs.lastRaiseSize = player.currentBet - previousBet;
        gs.minRaise = player.currentBet + gs.lastRaiseSize;
        gs.currentBet = player.currentBet;
        gs.lastRaiseIndex = (room._handPlayers || room.players).indexOf(player);
        (room._handPlayers || room.players).forEach(p => {
          if (p !== player && p.cards && p.cards.length > 0) p.hasActed = false;
        });
      }
      actionSucceeded = true;
      break;
  }

  player.handMaxBet = Math.max(player.handMaxBet, player.currentBet);
  player.hasActed = true;
  gs.pot = room.players.reduce((sum, p) => sum + (p.totalBet || 0), 0);
  moveToNextPlayer(room);
}

function moveToNextPlayer(room) {
  const gs = room.gameState;
  const handPlayers = room._handPlayers || room.players;
  const activePlayers = handPlayers.filter(p => p.cards && p.cards.length > 0);
  
  if (activePlayers.length <= 1) {
    const winner = activePlayers[0];
    if (winner) {
      const totalPot = room.players.reduce((sum, p) => sum + (p.totalBet || 0), 0);
      winner.stack += totalPot;
      winner.stats.wins++;
      winner.stats.maxWin = Math.max(winner.stats.maxWin, totalPot);
      winner.handResult = { name: 'Все сбросили', rank: -1, score: 0 };
      gs.pot = 0;
      gs.stage = 'showdown';
      gs.winners = [{ name: winner.name, hand: 'Все сбросили' }];
      room.players.forEach(syncPlayerToGlobal);
      saveGlobalStats();
      updateRoomState(room.id);
      setTimeout(() => {
        if (rooms.has(room.id)) {
          room.gameState = null;
          room.players = room.players.filter(p => !p.isBot);
          delete room._handPlayers;
          updateRoomState(room.id);
        }
      }, 30000);
    } else {
      gs.stage = 'showdown';
      updateRoomState(room.id);
    }
    return;
  }

  const allActed = activePlayers.every(p => p.hasActed);
  const allBetsEqual = activePlayers.every(p => p.currentBet === gs.currentBet);

  if (allActed && allBetsEqual) {
    if (gs.stage === 'preflop') { dealCommunityCards(room, 3); gs.stage = 'flop'; }
    else if (gs.stage === 'flop') { dealCommunityCards(room, 1); gs.stage = 'turn'; }
    else if (gs.stage === 'turn') { dealCommunityCards(room, 1); gs.stage = 'river'; }
    else if (gs.stage === 'river') { showdown(room); return; }
    room.players.forEach(p => { p.currentBet = 0; p.hasActed = false; });
    gs.currentBet = 0;
    gs.lastRaiseSize = 0;
    gs.minRaise = 0;
    gs.currentPlayerIndex = (room.dealerIndex + 1) % handPlayers.length;
    while (handPlayers[gs.currentPlayerIndex].cards.length === 0) {
      gs.currentPlayerIndex = (gs.currentPlayerIndex + 1) % handPlayers.length;
    }
  } else {
    let nextIndex = (gs.currentPlayerIndex + 1) % handPlayers.length;
    while (handPlayers[nextIndex].cards.length === 0) {
      nextIndex = (nextIndex + 1) % handPlayers.length;
    }
    gs.currentPlayerIndex = nextIndex;
  }

  updateRoomState(room.id);
  startTurnTimer(room);
  const nextPlayer = handPlayers[gs.currentPlayerIndex];
  if (nextPlayer && nextPlayer.isBot) {
    setTimeout(() => botAction(room), 1000 + Math.random() * 2000);
  }
}

function dealCommunityCards(room, count) {
  for (let i = 0; i < count; i++) room.gameState.communityCards.push(room.gameState.deck.pop());
}

function calculateSidePots(players) {
  const active = players.filter(p => p.cards && p.cards.length > 0);
  const betLevels = [...new Set(active.map(p => p.totalBet || 0).filter(b => b > 0))].sort((a, b) => a - b);
  const pots = [];
  let previousLevel = 0;

  for (const level of betLevels) {
    const contribution = level - previousLevel;
    const contributors = players.filter(p => (p.totalBet || 0) >= level);
    if (contributors.length === 0) continue;
    const potSize = contribution * contributors.length;
    const eligible = active.filter(p => (p.totalBet || 0) >= level);
    pots.push({ size: potSize, eligible });
    previousLevel = level;
  }

  const totalAssigned = pots.reduce((s, p) => s + p.size, 0);
  const mainPotTotal = players.reduce((sum, p) => sum + (p.totalBet || 0), 0);
  const remainder = mainPotTotal - totalAssigned;
  if (remainder > 0) {
    pots.push({ size: remainder, eligible: active });
  }

  return pots;
}

function showdown(room) {
  const gs = room.gameState;
  const activePlayers = room.players.filter(p => p.cards && p.cards.length > 0);
  activePlayers.forEach(p => {
    if (!p.stats) p.stats = { handsPlayed: 0, wins: 0, maxWin: 0, maxBet: 0, actions: 0 };
    p.stats.handsPlayed++;
    p.stats.maxBet = Math.max(p.stats.maxBet, p.handMaxBet || 0);
  });
  
  for (const player of activePlayers) {
    const allCards = [...player.cards, ...gs.communityCards];
    player.handResult = evaluateHand(allCards);
  }

  const sidePots = calculateSidePots(room.players);
  const allWinners = [];
  const countedWinners = new Set();

  for (const pot of sidePots) {
    if (pot.size === 0) continue;
    let bestScore = -1, bestPlayers = [];
    for (const player of pot.eligible) {
      if (player.handResult.score > bestScore) {
        bestScore = player.handResult.score;
        bestPlayers = [player];
      } else if (player.handResult.score === bestScore) {
        bestPlayers.push(player);
      }
    }
    const share = Math.floor(pot.size / bestPlayers.length);
    bestPlayers.forEach(w => {
      w.stack += share;
      if (!countedWinners.has(w)) {
        w.stats.wins++;
        countedWinners.add(w);
      }
      w.stats.maxWin = Math.max(w.stats.maxWin, share);
      allWinners.push({ name: w.name, hand: w.handResult.name });
    });
  }

  room.players.forEach(syncPlayerToGlobal);
  saveGlobalStats();
  gs.pot = 0;
  gs.stage = 'showdown';
  gs.winners = allWinners;
  updateRoomState(room.id);

  setTimeout(() => {
    if (rooms.has(room.id)) {
      room.gameState = null;
      room.players = room.players.filter(p => !p.isBot);
      delete room._handPlayers;
      updateRoomState(room.id);
    }
  }, 30000);
}

function updateRoomState(roomId) {
  const room = rooms.get(roomId);
  if (!room) return;
  room.lastActivity = Date.now();
  
  room.players.forEach(player => {
    if (player.isBot) return;
    const playerData = {
      roomId: room.id,
      players: room.players.map(p => ({
        id: p.id, name: sanitizeHtml(p.name), stack: p.stack, currentBet: p.currentBet,
        isActive: p.cards && p.cards.length > 0,
        seat: p.seat,
        isDealer: room.players.indexOf(p) === room.dealerIndex,
        connected: p.connected,
        isAdmin: p.isAdmin || false,
        isBot: p.isBot || false,
        position: p.position || '',
        cards: (p.id === player.id || (room.gameState && room.gameState.stage === 'showdown')) ? p.cards : [],
        handResult: (room.gameState && room.gameState.stage === 'showdown') ? p.handResult : null,
        stats: p.stats || { handsPlayed: 0, wins: 0, maxWin: 0, maxBet: 0, actions: 0 }
      })),
      gameState: room.gameState ? {
        communityCards: room.gameState.communityCards,
        pot: room.gameState.pot,
        currentBet: room.gameState.currentBet,
        stage: room.gameState.stage,
        minRaise: room.gameState.minRaise || room.gameState.currentBet * 2 || 0,
        currentPlayerId: room.gameState.currentPlayerIndex !== -1 ? (room._handPlayers || room.players)[room.gameState.currentPlayerIndex]?.id : null,
        turnDeadline: room.gameState.turnDeadline || null,
        winners: room.gameState.winners || null
      } : null,
      myId: player.id,
      isAdmin: player.isAdmin,
      myStats: { ...player.stats, stack: player.stack }
    };
    io.to(player.id).emit('updateGame', playerData);
  });
}

// ---- Сокеты ----
io.on('connection', (socket) => {
  console.log('User connected:', socket.id);

  socket.on('createRoom', (playerName, callback) => {
    if (!validatePlayerName(playerName)) {
      return callback({ success: false, message: 'Имя должно быть от 1 до 20 символов (буквы, цифры, пробелы, -,_)' });
    }
    if (rooms.size >= MAX_ROOMS) {
      return callback({ success: false, message: 'Достигнут лимит комнат' });
    }
    const roomId = generateRoomId();
      const nameKey = playerName.trim().toLowerCase();
      const savedStats = globalStats[nameKey] || { handsPlayed: 0, wins: 0, maxWin: 0, maxBet: 0, actions: 0, stack: 1000 };
      const restoredStack = savedStats.stack || 1000;
      const room = {
        id: roomId,
        players: [{
          id: socket.id, name: playerName.trim(), stack: restoredStack, cards: [], currentBet: 0,
          hasActed: false, connected: true, isAdmin: true, seat: 0,
          stats: { ...savedStats }
        }],
      gameState: null, turnTimer: null, startTimer: null, creator: socket.id,
      lastActivity: Date.now()
    };
    rooms.set(roomId, room);
    socketToRoom.set(socket.id, roomId);
    socket.join(roomId);
    saveRoom(roomId);
    callback({ success: true, roomId });
    updateRoomState(roomId);
  });

  socket.on('joinRoom', (data, callback) => {
    const { roomId, playerName } = data;
    if (!validatePlayerName(playerName)) {
      return callback({ success: false, message: 'Имя должно быть от 1 до 20 символов (буквы, цифры, пробелы, -,_)' });
    }
    if (!validateRoomId(roomId)) {
      return callback({ success: false, message: 'ID комнаты должен содержать 6 символов A-Z0-9' });
    }
    const room = rooms.get(roomId);
    if (!room) return callback({ success: false, message: 'Комната не найдена' });
    if (room.gameState && room.gameState.stage !== 'waiting')
      return callback({ success: false, message: 'Игра уже идёт, подождите следующую' });
    if (room.players.filter(p => !p.isBot).length >= MAX_PLAYERS_PER_ROOM || findAvailableSeat(room) === -1) {
      return callback({ success: false, message: 'Комната полна' });
    }

    let existing = room.players.find(p => p.id === socket.id);
    if (!existing) {
      const nameKey = playerName.trim().toLowerCase();
      existing = room.players.find(p => p.name && p.name.toLowerCase() === nameKey && !p.connected);
    }
    if (existing) {
      existing.id = socket.id;
      existing.connected = true; existing.name = playerName.trim(); socket.join(roomId);
      socketToRoom.set(socket.id, roomId);
    } else {
      const hasActiveAdmin = room.players.some(p => p.isAdmin && p.connected);
      const nameKey = playerName.trim().toLowerCase();
      const newSeat = findAvailableSeat(room);
      const savedStats = globalStats[nameKey] || { handsPlayed: 0, wins: 0, maxWin: 0, maxBet: 0, actions: 0, stack: 1000 };
      const restoredStack = savedStats.stack || 1000;
      const newPlayer = {
        id: socket.id, name: playerName.trim(), stack: restoredStack, cards: [], currentBet: 0,
        hasActed: false, connected: true, isAdmin: !hasActiveAdmin, seat: newSeat,
        stats: { ...savedStats }
      };
      room.players.push(newPlayer);
      socket.join(roomId);
      socketToRoom.set(socket.id, roomId);
    }
    room.players = room.players.filter(p => p.isBot || p.connected);
    saveRoom(roomId);
    callback({ success: true });
    updateRoomState(roomId);
  });

  socket.on('startGame', () => {
    const room = findRoomBySocket(socket);
    if (!room || room.creator !== socket.id) return;
    room.players = room.players.filter(p => !p.isBot);
    const humanPlayers = room.players.filter(p => !p.isBot);
    if (humanPlayers.length < 2) {
      const bot = {
        id: 'bot_' + Date.now(), name: BOT_NAMES[Math.floor(Math.random() * BOT_NAMES.length)],
        stack: 1000, cards: [], currentBet: 0, hasActed: false, connected: true, isAdmin: false, isBot: true,
        stats: { handsPlayed: 0, wins: 0, maxWin: 0, maxBet: 0, actions: 0 }
      };
      room.players.push(bot);
    }
    // Запускаем 10-секундный обратный отсчёт
    startGameCountdown(room);
  });

  socket.on('action', (actionData) => {
    const room = findRoomBySocket(socket);
    if (!room || !room.gameState) return;
    const { action, amount } = actionData;
    const handPlayers = room._handPlayers || room.players;
    const player = room.players.find(p => p.id === socket.id);
    if (!player || room.gameState.currentPlayerIndex === -1 || handPlayers[room.gameState.currentPlayerIndex].id !== socket.id) return;
    if (player.hasActed && action !== 'fold') return;
    if (!validateAction(action, amount, player, room.gameState)) return;
    processAction(room, player, action, amount);
  });

  socket.on('leaveRoom', () => {
    const room = findRoomBySocket(socket);
    if (!room) return;
    if (room.startTimer) clearTimeout(room.startTimer);
    if (room.turnTimer) clearTimeout(room.turnTimer);
    room.players = room.players.filter(p => p.id !== socket.id);
    socketToRoom.delete(socket.id);
    if (room.players.length === 0) {
      rooms.delete(room.id);
      delete roomsFromFile[room.id];
    } else {
      if (!room.players.some(p => p.isAdmin)) room.players[0].isAdmin = true;
      saveRoom(room.id);
    }
    socket.leave(room?.id);
    socket.emit('updateGame', { roomId: null, gameState: null, players: [] });
  });

  socket.on('leaveGame', () => {
    const room = findRoomBySocket(socket);
    if (!room || !room.gameState) return;
    if (room.turnTimer) clearTimeout(room.turnTimer);
    if (room.startTimer) clearTimeout(room.startTimer);
    room.gameState = null;
    saveRoom(room.id);
    updateRoomState(room.id);
  });

  socket.on('selectSeat', (seat, callback) => {
    const room = findRoomBySocket(socket);
    if (!room || room.gameState) return callback?.({ success: false, message: 'Игра уже идёт' });
    if (typeof seat !== 'number' || seat < 0 || seat >= MAX_PLAYERS_PER_ROOM)
      return callback?.({ success: false, message: 'Некорректное место' });
    const taken = room.players.filter(p => !p.isBot).some(p => p.seat === seat && p.id !== socket.id);
    if (taken) return callback?.({ success: false, message: 'Место занято' });
    const player = room.players.find(p => p.id === socket.id);
    if (player) player.seat = seat;
    saveRoom(room.id);
    updateRoomState(room.id);
    callback?.({ success: true });
  });

  socket.on('disconnect', () => {
    const room = findRoomBySocket(socket);
    if (room) {
      const player = room.players.find(p => p.id === socket.id);
      if (player) {
        player.connected = false;
        syncPlayerToGlobal(player);
        saveGlobalStats();
      }
      socketToRoom.delete(socket.id);
      updateRoomState(room.id);
    }
  });
});

function findRoomBySocket(socket) {
  const roomId = socketToRoom.get(socket.id);
  if (roomId) return rooms.get(roomId);
  for (const [id, room] of rooms) {
    if (room.players.some(p => p.id === socket.id)) return room;
  }
  return null;
}

function startNewHand(room) {
  room.players.forEach(p => { p.cards = []; p.currentBet = 0; p.hasActed = false; p.handMaxBet = 0; p.totalBet = 0; });
  const activePlayers = room.players.filter(p => p.connected && p.stack > 0);
  if (activePlayers.length < 2) {
    room.gameState = null;
    updateRoomState(room.id);
    return;
  }
  room._handPlayers = activePlayers;
  const deck = createDeck();
  room._handPlayers.forEach(p => p.cards = [deck.pop(), deck.pop()]);

  if (room.dealerIndex === undefined) room.dealerIndex = 0;
  else room.dealerIndex = (room.dealerIndex + 1) % room._handPlayers.length;

  const n = room._handPlayers.length;
  const positions = assignPositions(room._handPlayers, room.dealerIndex);
  room._handPlayers.forEach((p, i) => p.position = positions[i]);

  const sbPos = (room.dealerIndex + 1) % n;
  const bbPos = (room.dealerIndex + 2) % n;

  const sbPlayer = room._handPlayers[sbPos];
  const bbPlayer = room._handPlayers[bbPos];

  const sbBlind = Math.min(sbPlayer.stack, SB_AMOUNT);
  const bbBlind = Math.min(bbPlayer.stack, BB_AMOUNT);
  sbPlayer.stack -= sbBlind;
  sbPlayer.currentBet = sbBlind;
  sbPlayer.totalBet = (sbPlayer.totalBet || 0) + sbBlind;
  bbPlayer.stack -= bbBlind;
  bbPlayer.currentBet = bbBlind;
  bbPlayer.totalBet = (bbPlayer.totalBet || 0) + bbBlind;
  const pot = sbBlind + bbBlind;

  room.gameState = {
    deck, communityCards: [], pot,
    currentBet: bbBlind,
    smallBlind: SB_AMOUNT, bigBlind: BB_AMOUNT,
    stage: 'preflop',
    currentPlayerIndex: (bbPos + 1) % n,
    lastRaiseIndex: bbPos,
    lastRaiseSize: bbBlind,
    minRaise: bbBlind * 2,
    actionsInRound: []
  };

  room.players.forEach(p => p.hasActed = false);

  updateRoomState(room.id);
  startTurnTimer(room);
  const cp = room._handPlayers[room.gameState.currentPlayerIndex];
  if (cp && cp.isBot) setTimeout(() => botAction(room), 1200);
}

// ... вспомогательные функции
function createDeck() {
  const deck = [];
  for (const suit of SUITS) {
    for (const rank of RANKS) {
      deck.push({ suit, rank });
    }
  }
  return shuffle(deck);
}

function shuffle(array) {
  for (let i = array.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [array[i], array[j]] = [array[j], array[i]];
  }
  return array;
}

function getRankValue(rank) { return RANKS.indexOf(rank); }

function evaluateHand(cards) {
  if (cards.length < 5) return { rank: HAND_RANKS.HIGH_CARD, score: 0, name: 'Недостаточно карт' };
  const allCombos = getCombinations(cards, 5);
  let best = { rank: -1, score: 0, name: '' };
  for (const combo of allCombos) {
    const result = evaluateFiveCards(combo);
    if (result.rank > best.rank || (result.rank === best.rank && result.score > best.score)) {
      best = result;
    }
  }
  return best;
}

function getCombinations(arr, k) {
  if (k === 0) return [[]];
  if (arr.length < k) return [];
  const result = [];
  for (let i = 0; i <= arr.length - k; i++) {
    const head = arr.slice(i, i + 1);
    const tails = getCombinations(arr.slice(i + 1), k - 1);
    for (const tail of tails) result.push(head.concat(tail));
  }
  return result;
}

function evaluateFiveCards(cards) {
  const ranks = cards.map(c => getRankValue(c.rank)).sort((a, b) => a - b);
  const suits = cards.map(c => c.suit);
  const isFlush = new Set(suits).size === 1;
  const isStraight = checkStraight(ranks);
  const rankCounts = {};
  ranks.forEach(r => rankCounts[r] = (rankCounts[r] || 0) + 1);
  const counts = Object.values(rankCounts).sort((a, b) => b - a);
  const pairs = counts.filter(c => c === 2).length;
  const three = counts.includes(3);
  const four = counts.includes(4);

  let rank = HAND_RANKS.HIGH_CARD, name = 'Старшая карта', score = 0;
  const sortedByCountThenRank = Object.entries(rankCounts)
    .sort(([r1, c1], [r2, c2]) => c2 - c1 || parseInt(r2) - parseInt(r1))
    .map(([r]) => parseInt(r));

  if (isFlush && isStraight) {
    if (ranks[0] === 8 && ranks[4] === 12) { rank = HAND_RANKS.ROYAL_FLUSH; name = 'Роял-флеш'; score = 9 * 10**10; }
    else { rank = HAND_RANKS.STRAIGHT_FLUSH; name = 'Стрит-флеш'; score = 8 * 10**10 + (ranks[4] || 0); }
  } else if (four) {
    rank = HAND_RANKS.FOUR_OF_A_KIND; name = 'Каре';
    score = 7 * 10**10 + sortedByCountThenRank[0] * 10**5 + sortedByCountThenRank[1];
  } else if (three && pairs === 1) {
    rank = HAND_RANKS.FULL_HOUSE; name = 'Фулл-хаус';
    score = 6 * 10**10 + sortedByCountThenRank[0] * 10**5 + sortedByCountThenRank[1];
  } else if (isFlush) {
    rank = HAND_RANKS.FLUSH; name = 'Флеш';
    score = 5 * 10**10 + ranks[4]*10**8 + ranks[3]*10**6 + ranks[2]*10**4 + ranks[1]*10**2 + ranks[0];
  } else if (isStraight) {
    rank = HAND_RANKS.STRAIGHT; name = 'Стрит'; score = 4 * 10**10 + (ranks[4] || 0);
  } else if (three) {
    rank = HAND_RANKS.THREE_OF_A_KIND; name = 'Сет';
    score = 3 * 10**10 + sortedByCountThenRank[0]*10**8 + sortedByCountThenRank[1]*10**4 + sortedByCountThenRank[2];
  } else if (pairs === 2) {
    rank = HAND_RANKS.TWO_PAIR; name = 'Две пары';
    score = 2 * 10**10 + sortedByCountThenRank[0]*10**8 + sortedByCountThenRank[1]*10**4 + sortedByCountThenRank[2];
  } else if (pairs === 1) {
    rank = HAND_RANKS.ONE_PAIR; name = 'Пара';
    score = 1 * 10**10 + sortedByCountThenRank[0]*10**8 + sortedByCountThenRank[1]*10**5 + sortedByCountThenRank[2]*10**2 + sortedByCountThenRank[3];
  } else {
    score = ranks[4]*10**8 + ranks[3]*10**6 + ranks[2]*10**4 + ranks[1]*10**2 + ranks[0];
  }
  return { rank, score, name };
}

function checkStraight(sortedRanks) {
  if (sortedRanks.length !== 5) return false;
  if (sortedRanks[4] - sortedRanks[0] === 4 && new Set(sortedRanks).size === 5) return true;
  if (sortedRanks[0] === 0 && sortedRanks[1] === 1 && sortedRanks[2] === 2 && sortedRanks[3] === 3 && sortedRanks[4] === 12) return true;
  return false;
}

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`Покер-сервер запущен на http://localhost:${PORT}`));