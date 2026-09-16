// ==UserScript==
// @name         ♟ Patricia Chess Assistant - Stable Auto Move
// @namespace    PatriciaChessAssistant
// @version      3.0.0
// @description  Patricia chess engine assistant with safe turn detection, stale-result protection and delayed auto-move.
// @match        *://chess.com/*
// @match        *://*.chess.com/*
// @match        *://lichess.org/*
// @match        *://*.lichess.org/*
// @match        *://playstrategy.org/*
// @match        *://*.playstrategy.org/*
// @match        *://pychess.org/*
// @match        *://*.pychess.org/*
// @match        *://chess.org/*
// @match        *://*.chess.org/*
// @match        *://papergames.io/*
// @match        *://*.papergames.io/*
// @match        *://immortal.game/*
// @match        *://*.immortal.game/*
// @match        *://worldchess.com/*
// @match        *://*.worldchess.com/*
// @match        *://chess.net/*
// @match        *://*.chess.net/*
// @match        *://freechess.club/*
// @match        *://*.freechess.club/*
// @match        *://chess.coolmathgames.com/*
// @match        *://*.chess.coolmathgames.com/*
// @match        *://gameknot.com/*
// @match        *://*.gameknot.com/*
// @match        *://app.edchess.io/*
// @match        *://*.edchess.io/*
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_registerMenuCommand
// @run-at       document-idle
// ==/UserScript==

(function () {
    'use strict';

    /******************************************************************
     * CONFIGURATION
     ******************************************************************/

    const WS_URL = GM_getValue(
        'patriciaWsUrl',
        'wss://fi12.bot-hosting.cloud:25141'
    );

    const ENGINE_DEPTH = Number(
        GM_getValue('patriciaDepth', 15)
    );

    const ENGINE_MOVETIME = Number(
        GM_getValue('patriciaMoveTime', 1500)
    );

    const AUTO_MOVE = GM_getValue(
        'patriciaAutoMove',
        false
    );

    /*
     * IMPORTANT TIMINGS
     *
     * Position must remain unchanged for this long before analysis.
     */
    const POSITION_STABLE_DELAY = 700;

    /*
     * Patricia must return before this request expires.
     */
    const ENGINE_REQUEST_TIMEOUT = Math.max(
        5000,
        ENGINE_MOVETIME + 5000
    );

    /*
     * Delay after Patricia gives a move.
     *
     * This prevents:
     * - instant premoves
     * - clicking during animation
     * - moving before opponent's move is visually complete
     */
    const AUTO_MOVE_DELAY = 750;

    /*
     * Time between selecting source and destination.
     */
    const CLICK_DELAY = 280;

    /*
     * Safety lock after executing an automatic move.
     */
    const AUTO_MOVE_LOCK_TIME = 1200;

    /*
     * Do not repeatedly ask Patricia about the exact same position.
     */
    const SAME_POSITION_COOLDOWN = 1500;

    /******************************************************************
     * STATE
     ******************************************************************/

    let socket = null;
    let socketConnecting = false;

    let connected = false;

    /*
     * The side the player is playing.
     *
     * This is NOT the side to move.
     */
    let playerColor = null;

    /*
     * Current side to move.
     */
    let sideToMove = 'w';

    /*
     * Position state.
     */
    let currentFen = null;
    let currentBasicFen = null;

    let lastDetectedBasicFen = null;
    let positionVersion = 0;

    /*
     * Engine request state.
     */
    let requestCounter = 0;
    let activeRequest = null;

    /*
     * Auto-move state.
     */
    let autoMoveLock = false;
    let autoMoveTimer = null;

    /*
     * Position debounce.
     */
    let positionTimer = null;

    /*
     * Last position actually analyzed.
     */
    let lastAnalyzedFen = null;
    let lastAnalyzedAt = 0;

    /*
     * Board monitoring.
     */
    let observer = null;
    let scanTimer = null;

    /*
     * Drawing.
     */
    let arrowLayer = null;

    /*
     * Prevent excessive logging.
     */
    let lastStatus = '';

    /******************************************************************
     * LOGGING
     ******************************************************************/

    function log(...args) {
        console.log(
            '%c[Patricia]',
            'color:#8b5cf6;font-weight:bold',
            ...args
        );
    }

    function warn(...args) {
        console.warn(
            '%c[Patricia]',
            'color:#ef4444;font-weight:bold',
            ...args
        );
    }

    function status(text) {
        if (text === lastStatus) return;

        lastStatus = text;

        log(text);

        const el = document.getElementById(
            'patricia-status'
        );

        if (el) {
            el.textContent = text;
        }
    }

    /******************************************************************
     * UTILITIES
     ******************************************************************/

    function sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }

    function getBoardOrient() {
        /*
         * Chess.com
         */
        const board = document.querySelector(
            '.board'
        );

        if (board) {
            if (board.classList.contains('flipped')) {
                return 'b';
            }

            if (
                board.classList.contains('orientation-black')
            ) {
                return 'b';
            }

            if (
                board.classList.contains('orientation-white')
            ) {
                return 'w';
            }
        }

        /*
         * Lichess
         */
        const mainBoard = document.querySelector(
            'main .cg-wrap'
        );

        if (mainBoard) {
            const parent = mainBoard.closest(
                'div'
            );

            if (
                document.body.classList.contains(
                    'orientation-black'
                )
            ) {
                return 'b';
            }

            if (
                document.body.classList.contains(
                    'orientation-white'
                )
            ) {
                return 'w';
            }
        }

        /*
         * Generic board orientation.
         */
        const flipped = document.querySelector(
            '.board.flipped, .cg-wrap.flipped, [class*="orientation-black"]'
        );

        if (flipped) {
            return 'b';
        }

        return 'w';
    }

    function getPlayerColor() {
        return getBoardOrient();
    }

    /******************************************************************
     * FEN HELPERS
     ******************************************************************/

    function emptyBoard() {
        return Array.from(
            { length: 8 },
            () => Array(8).fill(null)
        );
    }

    function squareToCoords(square) {
        if (!square || square.length !== 2) {
            return null;
        }

        const file = square.charCodeAt(0) - 97;
        const rank = Number(square[1]);

        if (
            file < 0 ||
            file > 7 ||
            rank < 1 ||
            rank > 8
        ) {
            return null;
        }

        return {
            x: file,
            y: 8 - rank
        };
    }

    function coordsToSquare(x, y) {
        if (
            x < 0 ||
            x > 7 ||
            y < 0 ||
            y > 7
        ) {
            return null;
        }

        return (
            String.fromCharCode(97 + x) +
            String(8 - y)
        );
    }

    function parseFenBoard(fen) {
        const board = emptyBoard();

        if (!fen) {
            return board;
        }

        const boardPart = fen.split(/\s+/)[0];

        const ranks = boardPart.split('/');

        if (ranks.length !== 8) {
            return board;
        }

        for (let y = 0; y < 8; y++) {
            let x = 0;

            for (const char of ranks[y]) {
                if (/\d/.test(char)) {
                    x += Number(char);
                } else {
                    if (x >= 0 && x < 8) {
                        board[y][x] = char;
                    }

                    x++;
                }
            }
        }

        return board;
    }

    function normalizeBasicFen(fen) {
        if (!fen) return null;

        const parts = fen.trim().split(/\s+/);

        /*
         * Keep board only when our board extractor does not know
         * the complete FEN.
         */
        return parts[0] || null;
    }

    function buildFen(
        boardFen,
        turn,
        castling = '-',
        ep = '-',
        halfmove = '0',
        fullmove = '1'
    ) {
        return [
            boardFen,
            turn,
            castling,
            ep,
            halfmove,
            fullmove
        ].join(' ');
    }

    /******************************************************************
     * BOARD EXTRACTION
     ******************************************************************/

    function getChessBoardElement() {
        /*
         * Chess.com
         */
        const chessBoard =
            document.querySelector(
                '.board'
            );

        if (chessBoard) {
            return chessBoard;
        }

        /*
         * Lichess
         */
        const lichessBoard =
            document.querySelector(
                'cg-board'
            );

        if (lichessBoard) {
            return lichessBoard.closest(
                '.cg-wrap'
            ) || lichessBoard;
        }

        /*
         * Generic boards.
         */
        const selectors = [
            'chess-board',
            '.cg-wrap',
            '[data-board]',
            '.chess-board',
            '.board-container'
        ];

        for (const selector of selectors) {
            const el =
                document.querySelector(
                    selector
                );

            if (el) {
                return el;
            }
        }

        return null;
    }

    function getPieceElements(boardEl) {
        if (!boardEl) return [];

        /*
         * Chess.com pieces
         */
        let pieces =
            boardEl.querySelectorAll(
                '.piece'
            );

        if (pieces.length) {
            return Array.from(pieces);
        }

        /*
         * Lichess pieces.
         */
        pieces =
            boardEl.querySelectorAll(
                'piece'
            );

        if (pieces.length) {
            return Array.from(pieces);
        }

        /*
         * Generic.
         */
        pieces =
            boardEl.querySelectorAll(
                '[class*="piece"]'
            );

        return Array.from(pieces);
    }

    function pieceFromClassList(el) {
        if (!el) return null;

        const classes =
            Array.from(el.classList);

        /*
         * Typical Chess.com:
         *
         * piece wp square-e4
         * piece br square-a8
         */
        for (const cls of classes) {
            const match =
                cls.match(
                    /^([wb])([prnbqk])$/i
                );

            if (match) {
                return (
                    match[1].toLowerCase() === 'w'
                        ? match[2].toUpperCase()
                        : match[2].toLowerCase()
                );
            }
        }

        /*
         * Sometimes:
         *
         * white pawn
         * black queen
         */
        const joined =
            classes.join(' ').toLowerCase();

        const color =
            joined.includes('white')
                ? 'w'
                : joined.includes('black')
                    ? 'b'
                    : null;

        const pieceMap = [
            ['pawn', 'P'],
            ['knight', 'N'],
            ['bishop', 'B'],
            ['rook', 'R'],
            ['queen', 'Q'],
            ['king', 'K']
        ];

        if (color) {
            for (const [
                name,
                symbol
            ] of pieceMap) {
                if (
                    joined.includes(name)
                ) {
                    return color === 'w'
                        ? symbol
                        : symbol.toLowerCase();
                }
            }
        }

        return null;
    }

    function getPieceSquare(el) {
        if (!el) return null;

        const classes =
            Array.from(el.classList);

        for (const cls of classes) {
            const match =
                cls.match(
                    /^square-([a-h][1-8])$/i
                );

            if (match) {
                return match[1].toLowerCase();
            }
        }

        /*
         * data-square
         */
        const dataSquare =
            el.getAttribute(
                'data-square'
            );

        if (
            dataSquare &&
            /^[a-h][1-8]$/i.test(
                dataSquare
            )
        ) {
            return dataSquare.toLowerCase();
        }

        /*
         * Lichess often stores coordinates
         * with transform information instead.
         */
        return null;
    }

    function extractBoardFen() {
        const boardEl =
            getChessBoardElement();

        if (!boardEl) {
            return null;
        }

        const board =
            emptyBoard();

        const pieces =
            getPieceElements(
                boardEl
            );

        let found = 0;

        for (const piece of pieces) {
            const symbol =
                pieceFromClassList(
                    piece
                );

            const square =
                getPieceSquare(
                    piece
                );

            if (
                !symbol ||
                !square
            ) {
                continue;
            }

            const coords =
                squareToCoords(
                    square
                );

            if (!coords) {
                continue;
            }

            board[
                coords.y
            ][
                coords.x
            ] = symbol;

            found++;
        }

        if (found === 0) {
            return null;
        }

        return boardToFen(board);
    }

    function boardToFen(board) {
        const ranks = [];

        for (let y = 0; y < 8; y++) {
            let result = '';
            let empty = 0;

            for (let x = 0; x < 8; x++) {
                const piece =
                    board[y][x];

                if (!piece) {
                    empty++;
                    continue;
                }

                if (empty > 0) {
                    result += empty;
                    empty = 0;
                }

                result += piece;
            }

            if (empty > 0) {
                result += empty;
            }

            ranks.push(result);
        }

        return ranks.join('/');
    }

    /******************************************************************
     * TURN DETECTION
     ******************************************************************/

    function detectTurnFromPage() {
        /*
         * Lichess:
         *
         * The side-to-move often gets a "turn" class.
         */
        const turnElements =
            document.querySelectorAll(
                '.rclock.turn, .clock.turn, .is2d .rclock.turn'
            );

        if (turnElements.length) {
            for (const el of turnElements) {
                const classes =
                    Array.from(
                        el.classList
                    ).join(' ');

                if (
                    classes.includes(
                        'black'
                    )
                ) {
                    return 'b';
                }

                if (
                    classes.includes(
                        'white'
                    )
                ) {
                    return 'w';
                }
            }
        }

        /*
         * Chess.com clock turn detection.
         *
         * These selectors vary between versions,
         * so this is deliberately conservative.
         */
        const clocks =
            document.querySelectorAll(
                '[class*="clock"]'
            );

        for (const clock of clocks) {
            const cls =
                Array.from(
                    clock.classList
                ).join(' ')
                .toLowerCase();

            if (
                cls.includes('turn') ||
                cls.includes('active')
            ) {
                if (
                    cls.includes('black')
                ) {
                    return 'b';
                }

                if (
                    cls.includes('white')
                ) {
                    return 'w';
                }
            }
        }

        return null;
    }

    function initializeTurn() {
        const detected =
            detectTurnFromPage();

        if (detected) {
            sideToMove = detected;

            log(
                'Turn detected:',
                sideToMove
            );

            return;
        }

        /*
         * For a fresh chess game, White moves first.
         */
        sideToMove = 'w';

        log(
            'Turn detector unavailable. Starting from White.'
        );
    }

    function isOurTurn() {
        if (!playerColor) {
            playerColor =
                getPlayerColor();
        }

        return (
            playerColor ===
            sideToMove
        );
    }

    /******************************************************************
     * TURN UPDATE
     ******************************************************************/

    function updateTurnAfterPositionChange() {
        const detected =
            detectTurnFromPage();

        if (detected) {
            if (
                detected !==
                sideToMove
            ) {
                sideToMove =
                    detected;

                log(
                    'Turn changed by page detector:',
                    sideToMove
                );
            }

            return;
        }

        /*
         * Fallback:
         *
         * If the board position changes and
         * no explicit turn detector exists,
         * assume one legal move occurred.
         *
         * This is MUCH safer than using board
         * orientation as side-to-move.
         */
        sideToMove =
            sideToMove === 'w'
                ? 'b'
                : 'w';

        log(
            'Turn toggled:',
            sideToMove
        );
    }

    /******************************************************************
     * WEBSOCKET
     ******************************************************************/

    function connectSocket() {
        if (
            socketConnecting ||
            (
                socket &&
                (
                    socket.readyState ===
                    WebSocket.OPEN ||
                    socket.readyState ===
                    WebSocket.CONNECTING
                )
            )
        ) {
            return;
        }

        socketConnecting = true;

        status(
            'Connecting to Patricia...'
        );

        try {
            socket =
                new WebSocket(
                    WS_URL
                );
        } catch (err) {
            socketConnecting = false;

            warn(
                'WebSocket creation failed:',
                err
            );

            status(
                'WebSocket error'
            );

            scheduleReconnect();

            return;
        }

        socket.onopen = () => {
            socketConnecting = false;
            connected = true;

            status(
                'Patricia connected'
            );

            log(
                'Connected to:',
                WS_URL
            );

            /*
             * UCI initialization.
             */
            sendRaw('uci');

            setTimeout(() => {
                sendRaw('isready');
            }, 100);
        };

        socket.onmessage = event => {
            handleEngineMessage(
                event.data
            );
        };

        socket.onerror = error => {
            warn(
                'WebSocket error',
                error
            );

            status(
                'Patricia connection error'
            );
        };

        socket.onclose = () => {
            connected = false;
            socketConnecting = false;

            status(
                'Patricia disconnected'
            );

            scheduleReconnect();
        };
    }

    let reconnectTimer = null;

    function scheduleReconnect() {
        if (reconnectTimer) {
            return;
        }

        reconnectTimer =
            setTimeout(() => {
                reconnectTimer = null;

                connectSocket();
            }, 3000);
    }

    function sendRaw(command) {
        if (
            !socket ||
            socket.readyState !==
            WebSocket.OPEN
        ) {
            return false;
        }

        try {
            socket.send(command);
            return true;
        } catch (err) {
            warn(
                'WebSocket send failed:',
                err
            );

            return false;
        }
    }

    /******************************************************************
     * ENGINE REQUEST
     ******************************************************************/

    function requestBestMove(fen) {
        if (!fen) {
            return;
        }

        if (!connected) {
            connectSocket();
            return;
        }

        /*
         * Never request if it is not our turn when
         * auto mode is active.
         *
         * Manual analysis can still be enabled.
         */
        if (
            AUTO_MOVE &&
            !isOurTurn()
        ) {
            status(
                'Waiting for your turn...'
            );

            return;
        }

        /*
         * Prevent duplicate requests.
         */
        const now = Date.now();

        if (
            fen ===
            lastAnalyzedFen &&
            now - lastAnalyzedAt <
                SAME_POSITION_COOLDOWN
        ) {
            return;
        }

        /*
         * Cancel previous request logically.
         *
         * Patricia may still answer, but its response
         * will be rejected because request ID/version
         * no longer matches.
         */
        if (activeRequest) {
            activeRequest.cancelled =
                true;
        }

        const requestId =
            ++requestCounter;

        const version =
            positionVersion;

        activeRequest = {
            id: requestId,
            version,
            fen,
            createdAt: now,
            cancelled: false
        };

        lastAnalyzedFen = fen;
        lastAnalyzedAt = now;

        status(
            `Thinking... ${sideToMove === 'w' ? 'White' : 'Black'}`
        );

        /*
         * Standard UCI sequence.
         */
        sendRaw('stop');

        sendRaw(
            `position fen ${fen}`
        );

        sendRaw(
            `go depth ${ENGINE_DEPTH} movetime ${ENGINE_MOVETIME}`
        );

        /*
         * Safety timeout.
         */
        setTimeout(() => {
            if (
                activeRequest &&
                activeRequest.id ===
                    requestId
            ) {
                activeRequest = null;

                status(
                    'Engine request timed out'
                );
            }
        }, ENGINE_REQUEST_TIMEOUT);
    }

    /******************************************************************
     * ENGINE MESSAGE
     ******************************************************************/

    function handleEngineMessage(data) {
        if (!data) {
            return;
        }

        const lines =
            String(data)
                .split(/\r?\n/);

        for (const line of lines) {
            const trimmed =
                line.trim();

            if (
                !trimmed
            ) {
                continue;
            }

            if (
                trimmed.startsWith(
                    'bestmove'
                )
            ) {
                const parts =
                    trimmed.split(
                        /\s+/
                    );

                const move =
                    parts[1];

                if (
                    move &&
                    move !== '(none)'
                ) {
                    handleBestMove(
                        move
                    );
                }
            }
        }
    }

    /******************************************************************
     * BEST MOVE SAFETY CHECK
     ******************************************************************/

    function handleBestMove(move) {
        const request =
            activeRequest;

        if (!request) {
            log(
                'Ignoring bestmove: no active request'
            );

            return;
        }

        /*
         * Immediately invalidate request.
         */
        activeRequest = null;

        /*
         * Engine result must belong to the
         * exact position we requested.
         */
        if (
            request.version !==
            positionVersion
        ) {
            log(
                'Ignoring stale engine result: position changed'
            );

            return;
        }

        if (
            request.fen !==
            currentFen
        ) {
            log(
                'Ignoring stale engine result: FEN changed'
            );

            return;
        }

        /*
         * It must still be our turn.
         */
        if (
            !isOurTurn()
        ) {
            log(
                'Ignoring engine move: no longer our turn'
            );

            status(
                'Opponent moved first'
            );

            return;
        }

        /*
         * Validate UCI move format.
         */
        if (
            !/^[a-h][1-8][a-h][1-8][qrbn]?$/i.test(
                move
            )
        ) {
            warn(
                'Invalid engine move:',
                move
            );

            return;
        }

        status(
            `Patricia: ${move}`
        );

        log(
            'Best move:',
            move
        );

        /*
         * Manual mode:
         * show arrow only.
         */
        drawArrowFromMove(
            move
        );

        if (!AUTO_MOVE) {
            return;
        }

        /*
         * IMPORTANT:
         *
         * Do NOT move immediately.
         */
        scheduleSafeAutoMove(
            move,
            request
        );
    }

    /******************************************************************
     * SAFE AUTO MOVE
     ******************************************************************/

    function scheduleSafeAutoMove(
        move,
        request
    ) {
        if (autoMoveTimer) {
            clearTimeout(
                autoMoveTimer
            );

            autoMoveTimer = null;
        }

        if (autoMoveLock) {
            log(
                'Auto move locked'
            );

            return;
        }

        autoMoveTimer =
            setTimeout(async () => {
                autoMoveTimer = null;

                /*
                 * Re-check EVERYTHING.
                 */
                if (
                    request.version !==
                    positionVersion
                ) {
                    log(
                        'Cancelled auto move: position changed'
                    );

                    return;
                }

                if (
                    request.fen !==
                    currentFen
                ) {
                    log(
                        'Cancelled auto move: FEN changed'
                    );

                    return;
                }

                if (
                    !isOurTurn()
                ) {
                    log(
                        'Cancelled auto move: opponent turn'
                    );

                    return;
                }

                /*
                 * Re-read board immediately before clicking.
                 */
                const freshBoardFen =
                    extractBoardFen();

                if (
                    freshBoardFen &&
                    normalizeBasicFen(
                        freshBoardFen
                    ) !==
                    normalizeBasicFen(
                        request.fen
                    )
                ) {
                    log(
                        'Cancelled auto move: board changed'
                    );

                    return;
                }

                /*
                 * Lock.
                 */
                autoMoveLock = true;

                status(
                    `Playing ${move}...`
                );

                try {
                    await doAutoMove(
                        move
                    );
                } catch (err) {
                    warn(
                        'Auto move failed:',
                        err
                    );
                }

                setTimeout(() => {
                    autoMoveLock = false;
                }, AUTO_MOVE_LOCK_TIME);

            }, AUTO_MOVE_DELAY);
    }

    /******************************************************************
     * AUTO MOVE CLICKING
     ******************************************************************/

    async function doAutoMove(move) {
        if (!move) {
            return;
        }

        const from =
            move.slice(0, 2)
                .toLowerCase();

        const to =
            move.slice(2, 4)
                .toLowerCase();

        /*
         * Stop if board changed.
         */
        if (!isOurTurn()) {
            return;
        }

        /*
         * First click.
         */
        const fromElement =
            findSquareElement(
                from
            );

        const toElement =
            findSquareElement(
                to
            );

        if (
            !fromElement ||
            !toElement
        ) {
            warn(
                'Could not find move squares:',
                from,
                to
            );

            return;
        }

        /*
         * Move slower than the old script.
         */
        await sleep(120);

        if (!isOurTurn()) {
            return;
        }

        simulateClick(
            fromElement
        );

        /*
         * Give the site time to register
         * the selected piece.
         */
        await sleep(
            CLICK_DELAY
        );

        /*
         * The opponent cannot have moved between
         * these clicks, but still verify.
         */
        if (!isOurTurn()) {
            return;
        }

        /*
         * Make sure the board did not change.
         */
        const beforeDestination =
            extractBoardFen();

        if (
            beforeDestination &&
            currentFen &&
            normalizeBasicFen(
                beforeDestination
            ) !==
            normalizeBasicFen(
                currentFen
            )
        ) {
            warn(
                'Board changed before destination click'
            );

            return;
        }

        simulateClick(
            toElement
        );

        /*
         * Do NOT immediately request another move.
         *
         * Wait for the board observer to detect
         * the new position.
         */
        status(
            `Played ${move}`
        );
    }

    /******************************************************************
     * SQUARE FINDER
     ******************************************************************/

    function findSquareElement(
        square
    ) {
        const board =
            getChessBoardElement();

        if (!board) {
            return null;
        }

        /*
         * Chess.com
         */
        let el =
            board.querySelector(
                `.square-${square}`
            );

        if (el) {
            return el;
        }

        /*
         * Generic data-square.
         */
        el =
            board.querySelector(
                `[data-square="${square}"]`
            );

        if (el) {
            return el;
        }

        /*
         * Lichess:
         *
         * Convert algebraic square to coordinates
         * and use the board's visual geometry.
         */
        return findSquareByGeometry(
            board,
            square
        );
    }

    function findSquareByGeometry(
        board,
        square
    ) {
        const rect =
            board.getBoundingClientRect();

        if (
            !rect.width ||
            !rect.height
        ) {
            return null;
        }

        const squareSize =
            Math.min(
                rect.width,
                rect.height
            ) / 8;

        const coords =
            squareToCoords(
                square
            );

        if (!coords) {
            return null;
        }

        let x =
            coords.x;

        let y =
            coords.y;

        if (
            getBoardOrient() ===
            'b'
        ) {
            x = 7 - x;
            y = 7 - y;
        }

        const centerX =
            rect.left +
            x * squareSize +
            squareSize / 2;

        const centerY =
            rect.top +
            y * squareSize +
            squareSize / 2;

        const element =
            document.elementFromPoint(
                centerX,
                centerY
            );

        return (
            element ||
            null
        );
    }

    /******************************************************************
     * CLICK SIMULATION
     ******************************************************************/

    function simulateClick(
        element
    ) {
        if (!element) {
            return;
        }

        const rect =
            element.getBoundingClientRect();

        const x =
            rect.left +
            rect.width / 2;

        const y =
            rect.top +
            rect.height / 2;

        const events = [
            'pointerdown',
            'mousedown',
            'pointerup',
            'mouseup',
            'click'
        ];

        for (const type of events) {
            let event;

            if (
                type.startsWith(
                    'pointer'
                )
            ) {
                event =
                    new PointerEvent(
                        type,
                        {
                            bubbles: true,
                            cancelable: true,
                            composed: true,
                            clientX: x,
                            clientY: y,
                            pointerId: 1,
                            pointerType: 'mouse',
                            isPrimary: true,
                            buttons:
                                type ===
                                'pointerdown'
                                    ? 1
                                    : 0
                        }
                    );
            } else {
                event =
                    new MouseEvent(
                        type,
                        {
                            bubbles: true,
                            cancelable: true,
                            composed: true,
                            clientX: x,
                            clientY: y,
                            button: 0
                        }
                    );
            }

            element.dispatchEvent(
                event
            );
        }
    }

    /******************************************************************
     * ARROW DRAWING
     ******************************************************************/

    function createArrowLayer() {
        if (arrowLayer) {
            return arrowLayer;
        }

        const board =
            getChessBoardElement();

        if (!board) {
            return null;
        }

        arrowLayer =
            document.createElement(
                'div'
            );

        arrowLayer.id =
            'patricia-arrow-layer';

        Object.assign(
            arrowLayer.style,
            {
                position: 'absolute',
                inset: '0',
                pointerEvents: 'none',
                zIndex: '99999'
            }
        );

        const computed =
            getComputedStyle(
                board
            );

        if (
            computed.position ===
            'static'
        ) {
            board.style.position =
                'relative';
        }

        board.appendChild(
            arrowLayer
        );

        return arrowLayer;
    }

    function clearArrow() {
        if (
            arrowLayer
        ) {
            arrowLayer.innerHTML =
                '';
        }
    }

    function drawArrowFromMove(
        move
    ) {
        clearArrow();

        if (
            !move ||
            move.length < 4
        ) {
            return;
        }

        const from =
            move.slice(0, 2)
                .toLowerCase();

        const to =
            move.slice(2, 4)
                .toLowerCase();

        const board =
            getChessBoardElement();

        if (!board) {
            return;
        }

        const layer =
            createArrowLayer();

        if (!layer) {
            return;
        }

        const boardRect =
            board.getBoundingClientRect();

        if (
            !boardRect.width ||
            !boardRect.height
        ) {
            return;
        }

        const squareSize =
            boardRect.width / 8;

        const fromCoords =
            squareToCoords(
                from
            );

        const toCoords =
            squareToCoords(
                to
            );

        if (
            !fromCoords ||
            !toCoords
        ) {
            return;
        }

        let fx =
            fromCoords.x;

        let fy =
            fromCoords.y;

        let tx =
            toCoords.x;

        let ty =
            toCoords.y;

        if (
            getBoardOrient() ===
            'b'
        ) {
            fx = 7 - fx;
            fy = 7 - fy;
            tx = 7 - tx;
            ty = 7 - ty;
        }

        const x1 =
            fx * squareSize +
            squareSize / 2;

        const y1 =
            fy * squareSize +
            squareSize / 2;

        const x2 =
            tx * squareSize +
            squareSize / 2;

        const y2 =
            ty * squareSize +
            squareSize / 2;

        const dx =
            x2 - x1;

        const dy =
            y2 - y1;

        const length =
            Math.sqrt(
                dx * dx +
                dy * dy
            );

        const angle =
            Math.atan2(
                dy,
                dx
            ) *
            180 /
            Math.PI;

        const arrow =
            document.createElement(
                'div'
            );

        Object.assign(
            arrow.style,
            {
                position: 'absolute',
                left: `${x1}px`,
                top: `${y1}px`,
                width: `${length}px`,
                height: '8px',
                transformOrigin: '0 50%',
                transform:
                    `rotate(${angle}deg)`,
                background:
                    'rgba(80, 200, 120, 0.85)',
                borderRadius: '999px',
                filter:
                    'drop-shadow(0 0 4px rgba(0,0,0,.5))'
            }
        );

        const head =
            document.createElement(
                'div'
            );

        Object.assign(
            head.style,
            {
                position: 'absolute',
                right: '-2px',
                top: '-7px',
                width: '0',
                height: '0',
                borderTop:
                    '11px solid transparent',
                borderBottom:
                    '11px solid transparent',
                borderLeft:
                    '18px solid rgba(80, 200, 120, 0.85)'
            }
        );

        arrow.appendChild(
            head
        );

        layer.appendChild(
            arrow
        );
    }

    /******************************************************************
     * POSITION MONITOR
     ******************************************************************/

    function checkPosition() {
        const boardFen =
            extractBoardFen();

        if (!boardFen) {
            return;
        }

        const basicFen =
            normalizeBasicFen(
                boardFen
            );

        if (!basicFen) {
            return;
        }

        /*
         * First detection.
         */
        if (
            lastDetectedBasicFen ===
            null
        ) {
            lastDetectedBasicFen =
                basicFen;

            currentBasicFen =
                basicFen;

            currentFen =
                buildFen(
                    basicFen,
                    sideToMove
                );

            positionVersion++;

            status(
                'Board detected'
            );

            return;
        }

        /*
         * Nothing changed.
         */
        if (
            basicFen ===
            lastDetectedBasicFen
        ) {
            return;
        }

        /*
         * Position changed.
         */
        lastDetectedBasicFen =
            basicFen;

        positionVersion++;

        /*
         * Cancel any pending auto move.
         */
        if (autoMoveTimer) {
            clearTimeout(
                autoMoveTimer
            );

            autoMoveTimer = null;
        }

        /*
         * Cancel active engine request logically.
         */
        if (activeRequest) {
            activeRequest.cancelled =
                true;

            activeRequest =
                null;
        }

        /*
         * Clear old arrow.
         */
        clearArrow();

        /*
         * Update side to move.
         */
        updateTurnAfterPositionChange();

        currentBasicFen =
            basicFen;

        /*
         * Build the current FEN.
         */
        currentFen =
            buildFen(
                basicFen,
                sideToMove
            );

        /*
         * Wait for the board animation to finish.
         */
        if (positionTimer) {
            clearTimeout(
                positionTimer
            );
        }

        const versionAtDetection =
            positionVersion;

        const fenAtDetection =
            currentFen;

        positionTimer =
            setTimeout(() => {
                positionTimer =
                    null;

                /*
                 * Board must still be the same.
                 */
                if (
                    versionAtDetection !==
                    positionVersion
                ) {
                    return;
                }

                const latest =
                    extractBoardFen();

                if (
                    latest &&
                    normalizeBasicFen(
                        latest
                    ) !==
                    normalizeBasicFen(
                        fenAtDetection
                    )
                ) {
                    return;
                }

                /*
                 * If auto mode is enabled,
                 * only analyze our turn.
                 */
                if (
                    AUTO_MOVE &&
                    !isOurTurn()
                ) {
                    status(
                        'Waiting for opponent...'
                    );

                    return;
                }

                requestBestMove(
                    fenAtDetection
                );

            }, POSITION_STABLE_DELAY);
    }

    function startPositionMonitor() {
        if (observer) {
            return;
        }

        const target =
            document.body;

        if (!target) {
            return;
        }

        observer =
            new MutationObserver(
                () => {
                    if (
                        scanTimer
                    ) {
                        return;
                    }

                    scanTimer =
                        setTimeout(
                            () => {
                                scanTimer =
                                    null;

                                checkPosition();
                            },
                            150
                        );
                }
            );

        observer.observe(
            target,
            {
                subtree: true,
                childList: true,
                attributes: true,
                attributeFilter: [
                    'class',
                    'style',
                    'data-square'
                ]
            }
        );

        /*
         * Also periodically check because
         * some chess boards use canvas/Shadow DOM.
         */
        setInterval(
            checkPosition,
            1000
        );

        checkPosition();
    }

    /******************************************************************
     * UI
     ******************************************************************/

    function createUI() {
        if (
            document.getElementById(
                'patricia-panel'
            )
        ) {
            return;
        }

        const panel =
            document.createElement(
                'div'
            );

        panel.id =
            'patricia-panel';

        Object.assign(
            panel.style,
            {
                position: 'fixed',
                right: '15px',
                bottom: '15px',
                width: '230px',
                padding: '12px',
                background:
                    'rgba(20,20,25,.94)',
                color: '#fff',
                borderRadius: '12px',
                fontFamily:
                    'Arial, sans-serif',
                fontSize: '12px',
                zIndex: '2147483647',
                boxShadow:
                    '0 8px 30px rgba(0,0,0,.45)',
                backdropFilter:
                    'blur(10px)'
            }
        );

        panel.innerHTML = `
            <div style="
                font-size:15px;
                font-weight:bold;
                margin-bottom:7px;
            ">
                ♟ Patricia
            </div>

            <div id="patricia-status"
                 style="
                    opacity:.8;
                    margin-bottom:8px;
                 ">
                Starting...
            </div>

            <div style="
                display:grid;
                grid-template-columns:1fr 1fr;
                gap:5px;
                margin-bottom:7px;
            ">
                <div>
                    You:
                    <b id="patricia-player">?</b>
                </div>

                <div>
                    Turn:
                    <b id="patricia-turn">?</b>
                </div>
            </div>

            <div style="
                display:flex;
                gap:5px;
            ">
                <button id="patricia-connect">
                    Connect
                </button>

                <button id="patricia-clear">
                    Clear
                </button>
            </div>
        `;

        document.body.appendChild(
            panel
        );

        const buttons =
            panel.querySelectorAll(
                'button'
            );

        buttons.forEach(button => {
            Object.assign(
                button.style,
                {
                    flex: '1',
                    padding: '6px',
                    border: '0',
                    borderRadius: '7px',
                    cursor: 'pointer'
                }
            );
        });

        const connect =
            document.getElementById(
                'patricia-connect'
            );

        connect.onclick = () => {
            connectSocket();
        };

        const clear =
            document.getElementById(
                'patricia-clear'
            );

        clear.onclick = () => {
            clearArrow();

            if (
                activeRequest
            ) {
                activeRequest.cancelled =
                    true;

                activeRequest =
                    null;
            }

            status(
                'Arrow cleared'
            );
        });

        updateUI();
    }

    function updateUI() {
        const player =
            document.getElementById(
                'patricia-player'
            );

        const turn =
            document.getElementById(
                'patricia-turn'
            );

        if (player) {
            player.textContent =
                playerColor === 'w'
                    ? 'White'
                    : playerColor === 'b'
                        ? 'Black'
                        : '?';
        }

        if (turn) {
            turn.textContent =
                sideToMove === 'w'
                    ? 'White'
                    : 'Black';
        }
    }

    setInterval(
        updateUI,
        500
    );

    /******************************************************************
     * MENU
     ******************************************************************/

    GM_registerMenuCommand(
        'Set Patricia WebSocket URL',
        () => {
            const value =
                prompt(
                    'Patricia WebSocket URL:',
                    WS_URL
                );

            if (
                value &&
                value.trim()
            ) {
                GM_setValue(
                    'patriciaWsUrl',
                    value.trim()
                );

                alert(
                    'Saved. Reload the page.'
                );
            }
        }
    );

    GM_registerMenuCommand(
        'Set Engine Depth',
        () => {
            const value =
                prompt(
                    'Engine depth:',
                    String(
                        ENGINE_DEPTH
                    )
                );

            const depth =
                Number(value);

            if (
                Number.isFinite(
                    depth
                ) &&
                depth > 0
            ) {
                GM_setValue(
                    'patriciaDepth',
                    Math.floor(depth)
                );

                alert(
                    'Saved. Reload the page.'
                );
            }
        }
    );

    GM_registerMenuCommand(
        'Set Engine Move Time',
        () => {
            const value =
                prompt(
                    'Engine movetime in milliseconds:',
                    String(
                        ENGINE_MOVETIME
                    )
                );

            const time =
                Number(value);

            if (
                Number.isFinite(
                    time
                ) &&
                time >= 100
            ) {
                GM_setValue(
                    'patriciaMoveTime',
                    Math.floor(time)
                );

                alert(
                    'Saved. Reload the page.'
                );
            }
        }
    );

    GM_registerMenuCommand(
        AUTO_MOVE
            ? 'Disable Auto Move'
            : 'Enable Auto Move',
        () => {
            GM_setValue(
                'patriciaAutoMove',
                !AUTO_MOVE
            );

            alert(
                `Auto Move ${
                    !AUTO_MOVE
                        ? 'enabled'
                        : 'disabled'
                }. Reload the page.`
            );
        }
    );

    /******************************************************************
     * INITIALIZATION
     ******************************************************************/

    function initialize() {
        log(
            'Patricia Chess Assistant v3.0'
        );

        log(
            'WebSocket:',
            WS_URL
        );

        log(
            'Depth:',
            ENGINE_DEPTH
        );

        log(
            'Movetime:',
            ENGINE_MOVETIME
        );

        log(
            'Auto move:',
            AUTO_MOVE
        );

        playerColor =
            getPlayerColor();

        initializeTurn();

        createUI();

        updateUI();

        connectSocket();

        /*
         * Give the chess site a moment to
         * finish rendering its board.
         */
        setTimeout(() => {
            playerColor =
                getPlayerColor();

            startPositionMonitor();

            updateUI();
        }, 1500);
    }

    if (
        document.readyState ===
        'loading'
    ) {
        document.addEventListener(
            'DOMContentLoaded',
            initialize
        );
    } else {
        initialize();
    }

})();
