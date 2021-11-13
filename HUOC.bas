'HUOC: Huo Chess by Spiros I. Kakos (huo) - DRAFT VERSION (NOT FULLY TESTED, STILL IN PROGRESS)

'Version 0.2: Thinking in 3 half-moves depth
'Version 0.3: Thinking in 3 half-moves depth with MinMax algorithm
'Version 0.4: Thinking up to 5 half-moves depth
'Version 0.5: Improved score function
'Version 0.6: Added opening functionality

'Based on the Huo Chess implementation in C++ and C#
'Check "Huo Chess" in C# at Harmonia Philosophica for code in C# and relative tutorials
'Check https://harmoniaphilosophica.com/2019/02/13/huo-chess-c-micro-chess-updated/

'Other QBasic Internet resources
'https://www.qb64.org/wiki/Arrays#Working_with_the_Array_Elements
'https://www.qb64.org/wiki/CALL
'https://www.qb64.org/wiki/SUB
'https://www.qb64.org/wiki/IF...THEN

'What is not supported...
'1. En passant [FIXED: 2020-08-06 - Not included in computer thought!]
'2. Castling [FIXED only for human player: 2020-08-04 - Not included in computer thought!]
'3. Pawn promotion [FIXED only for queen promotion: 2020-08-04 - Not included in computer thought!]
'4. Check [FIXED: 2020-08-05 - Not included in computer thought!]
'5. Mate [FIXED: 2020-08-05 - Not included in computer thought!]
'6. Inform user he has entered an invalid move [FIXED: 2020-08-06]

DECLARE SUB movValidation (aline AS INTEGER, fline AS INTEGER, arcol AS INTEGER, telcol AS INTEGER)
DECLARE SUB drawBoard ()
DECLARE SUB ElegxosNomimotitas(ENSkakiera() AS STRING, startColumn AS INTEGER, startRank AS INTEGER, finishColumn AS INTEGER, finishRank AS INTEGER, MovingPieceEN AS STRING)

DEFINT A-Z
OPTION BASE 1 'Make tables dimensions start from 1

DIM SHARED chessboard$(8, 8)
COMMON SHARED playerColor$
COMMON SHARED startingRank, startingColumn
COMMON SHARED finishingRank, finishingColumn
COMMON SHARED startingRankText$, startingColumnText$
COMMON SHARED finishingRankText$, finishingColumnText$
COMMON SHARED Move$
COMMON SHARED MovingPiece$
COMMON SHARED ProsorinoKommati$
COMMON SHARED Nomimotita
COMMON SHARED debugMode
COMMON SHARED positionScore
COMMON SHARED bestStartingRank, bestStartingColumn
COMMON SHARED bestFinishingRank, bestFinishingColumn
COMMON SHARED bestStartingRankMate, bestStartingColumnMate '14/3/2021
COMMON SHARED bestFinishingRankMate, bestFinishingColumnMate '14/3/2021
COMMON SHARED bestPositionScore
COMMON SHARED whoPlays$
COMMON SHARED whichColorPlays$ '14/3/2021
COMMON SHARED computerLogs$, humanLogs$
COMMON SHARED MoveNumber
'Castling
COMMON SHARED whiteCastling
COMMON SHARED whiteBigCastling
COMMON SHARED whiteSmallCastling
COMMON SHARED blackCastling
COMMON SHARED blackBigCastling
COMMON SHARED blackSmallCastling
'Check variables
COMMON SHARED whiteCheck
COMMON SHARED blackCheck
'En passant
COMMON SHARED enPassantColumn
COMMON SHARED enPassantRank
COMMON SHARED enPassantHappened
'COMMON SHARED enPassantTest
COMMON SHARED MateFound '14/3/2021
COMMON SHARED PatFound '14/3/2021
COMMON SHARED HumanMoveFound '14/3/2021
'MinMax
'Important note: All dimensions in the tables are +1 compared to the Huo Chess in C#! (tables start from 1 here)
COMMON SHARED foundMove
DIM SHARED NodesAnalysis0(1000000, 6)
DIM SHARED NodesAnalysis1(1000000, 2)
DIM SHARED NodesAnalysis2(1000000, 2)
DIM SHARED NodesAnalysis3(10000000, 2) AS LONG
DIM SHARED NodesAnalysis4(10000000, 2) AS LONG
COMMON SHARED NodeLevel_0_count AS LONG
COMMON SHARED NodeLevel_1_count AS LONG
COMMON SHARED NodeLevel_2_count AS LONG
COMMON SHARED NodeLevel_3_count AS LONG
COMMON SHARED NodeLevel_4_count AS LONG
COMMON SHARED parentNodeAnalyzed AS LONG
DIM SHARED bestNodes0(10000000)
DIM SHARED bestNodes1(10000000)
DIM SHARED bestNodes2(10000000)
DIM SHARED bestNodes3(10000000)
DIM SHARED bestNodes4(10000000)
COMMON SHARED bestNode2, bestNode1, bestNode0
COMMON SHARED counter0 AS LONG
COMMON SHARED counter1 AS LONG
COMMON SHARED counter2 AS LONG
COMMON SHARED counter3 AS LONG
COMMON SHARED counter4 AS LONG
COMMON SHARED huologs$, logLine$

COMMON SHARED thinkingDepth
COMMON SHARED Move
COMMON SHARED CalledFromCheckCheck '14/3/2021

'Set debugMode = 1 if you want debugging messages to appear, else set to 0
debugMode = 0

PRINT "Huo Chess - HUOC v0.6 by Spiros Kakos (2020, 2021)"
PRINT ""
PRINT "The best open source chess in BASIC for educational purposes"
PRINT "Check HUO CHESS in C# at Harmonia Philosophica as well!"
PRINT ""
PRINT "How to play: Enter move coordinates without spaces (e.g. c2c4) and press Enter"
PRINT ""

SetPlayerColor:
'Set the colour of the player
INPUT "Set your color. Please select 'w' or 'b': ", playerColor$
IF playerColor$ <> "w" AND playerColor$ <> "b" THEN GOTO SetPlayerColor

SetThinkingDepth:
'Set the thinking depth
PRINT "": INPUT "Set thinking depth. Please select 1 or 3 or 5: ", thinkingDepth
IF thinkingDepth <> 1 AND thinkingDepth <> 3 AND thinkingDepth <> 5 THEN GOTO SetThinkingDepth

PRINT ""
computerLogs:
INPUT "Activate debug messages for computer?  (y/n) ", computerLogs$: IF computerLogs$ <> "y" AND computerLogs$ <> "n" THEN GOTO computerLogs
humanLogs:
INPUT "Activate debug messages for the human? (y/n) ", humanLogs$: IF humanLogs$ <> "y" AND humanLogs$ <> "n" THEN GOTO humanLogs

CLS

CALL initialPosition
CALL drawBoard

'Initialize variables
MoveNumber = 0
'Check variables
whiteCheck = 0
blackCheck = 0
'Castling
whiteCastling = 0
blackCastling = 0
whiteBigCastling = 0
whiteSmallCastling = 0
blackBigCastling = 0
blackSmallCastling = 0
'En Passant
'enPassantTest = 0
enPassantHappened = 0
CHDIR "Huo Chess Opening Book"

'Set thinking depth
'thinkingDepth = 3

LOCATE 12, 1: PRINT "Huo Chess - HUOC"

IF playerColor$ = "w" THEN
    whoPlays$ = "Human"
    CALL PlayerMove
END IF

IF playerColor$ = "b" THEN
    whoPlays$ = "HY"
    LOCATE 13, 1: PRINT "Thinking..."
    CALL computerMove
END IF

SUB PlayerMove

    'Initialize variables
    'Check
    whiteCheck = 0
    blackCheck = 0
    'En Passant
    enPassantHappened = 0

    IF playerColor$ = "b" THEN whichColorPlays$ = "Black" '14/3/2021
    IF playerColor$ = "w" THEN whichColorPlays$ = "White" '14/3/2021

    'Check the Check
    IF playerColor$ = "b" THEN CALL checkBlackCheck(chessboard$())
    IF playerColor$ = "w" THEN CALL checkWhiteCheck(chessboard$())
    'PRINT "PlayerMove: blackCheck = " + STR$(blackCheck): INPUT aa$
    IF whiteCheck = 1 OR blackCheck = 1 THEN LOCATE 12, 1: PRINT "Check!            ": LOCATE 13, 1: PRINT "Press Enter": DO: LOOP UNTIL INKEY$ <> "": LOCATE 12, 1: PRINT "                 ": LOCATE 13, 1: PRINT "           "

    LOCATE 13, 1: INPUT "Enter your move: ", Move$
    startingColumnText$ = MID$(Move$, 1, 1)
    startingRankText$ = MID$(Move$, 2, 1)
    finishingColumnText$ = MID$(Move$, 3, 1)
    finishingRankText$ = MID$(Move$, 4, 1)

    IF humanLogs$ = "y" THEN debugMode = 1 ELSE debugMode = 0

    SELECT CASE startingRankText$
        CASE "1"
            startingRank = 1
        CASE "2"
            startingRank = 2
        CASE "3"
            startingRank = 3
        CASE "4"
            startingRank = 4
        CASE "5"
            startingRank = 5
        CASE "6"
            startingRank = 6
        CASE "7"
            startingRank = 7
        CASE "8"
            startingRank = 8
    END SELECT

    SELECT CASE finishingRankText$
        CASE "1"
            finishingRank = 1
        CASE "2"
            finishingRank = 2
        CASE "3"
            finishingRank = 3
        CASE "4"
            finishingRank = 4
        CASE "5"
            finishingRank = 5
        CASE "6"
            finishingRank = 6
        CASE "7"
            finishingRank = 7
        CASE "8"
            finishingRank = 8
    END SELECT

    SELECT CASE startingColumnText$
        CASE "A", "a"
            startingColumn = 1
        CASE "B", "b"
            startingColumn = 2
        CASE "C", "c"
            startingColumn = 3
        CASE "D", "d"
            startingColumn = 4
        CASE "E", "e"
            startingColumn = 5
        CASE "F", "f"
            startingColumn = 6
        CASE "G", "g"
            startingColumn = 7
        CASE "H", "h"
            startingColumn = 8
    END SELECT

    SELECT CASE finishingColumnText$
        CASE "A", "a"
            finishingColumn = 1
        CASE "B", "b"
            finishingColumn = 2
        CASE "C", "c"
            finishingColumn = 3
        CASE "D", "d"
            finishingColumn = 4
        CASE "E", "e"
            finishingColumn = 5
        CASE "F", "f"
            finishingColumn = 6
        CASE "G", "g"
            finishingColumn = 7
        CASE "H", "h"
            finishingColumn = 8
    END SELECT

    MovingPiece$ = chessboard$(startingColumn, startingRank)
    ProsorinoKommati$ = chessboard$(finishingColumn, finishingRank)

    IF (debugMode = 1) THEN
        PRINT "[Move: " + STR$(startingColumn) + STR$(startingRank) + " -> " + STR$(finishingColumn) + STR$(finishingRank) + " ]"
    END IF

    'Check legality of the move entered
    CalledFromCheckCheck = 0 '14/3/2021
    CALL ElegxosNomimotitas(chessboard$(), 0, startingColumn, startingRank, finishingColumn, finishingRank, MovingPiece$)

    ' ------------------ Check the Check! START ------------------

    'Temporarily do the move
    chessboard$(finishingColumn, finishingRank) = chessboard$(startingColumn, startingRank)
    chessboard$(startingColumn, startingRank) = ""

    'Check the check
    IF playerColor$ = "b" AND Nomimotita = 1 THEN
        whoPlays$ = "HY"
        CALL checkBlackCheck(chessboard$())
        'Restore Nomimotita! (because it is 'broken' in the checkCheck function
        Nomimotita = 1
        IF blackCheck = 1 THEN Nomimotita = 0
        whoPlays$ = "Human"
    END IF

    IF playerColor$ = "w" AND Nomimotita = 1 THEN
        whoPlays$ = "HY"
        CALL checkWhiteCheck(chessboard$())
        'Restore Nomimotita! (because it is 'broken' in the checkCheck function
        Nomimotita = 1
        IF whiteCheck = 1 THEN Nomimotita = 0
        whoPlays$ = "Human"
    END IF

    'Undo the move
    chessboard$(startingColumn, startingRank) = MovingPiece$
    chessboard$(finishingColumn, finishingRank) = ProsorinoKommati$

    ' ------------------ Check the Check! END ------------------

    'Castling
    IF (playerColor$ = "w" AND whiteCastling = 0) OR (playerColor$ = "b" AND blackCastling = 0) THEN CALL Castling
    IF playerColor$ = "w" AND whiteCastling = 1 THEN Nomimotita = 1
    IF playerColor$ = "b" AND blackCastling = 1 THEN Nomimotita = 1

    'If move is legal, then do the move and present it in the chessbooard
    IF Nomimotita = 1 THEN

        IF debugMode = 1 THEN
            PRINT "Now we will redraw the chessboard"
        END IF

        'Do the move
        chessboard$(finishingColumn, finishingRank) = chessboard$(startingColumn, startingRank)
        chessboard$(startingColumn, startingRank) = ""

        'Castling
        IF playerColor$ = "w" AND whiteBigCastling = 1 THEN chessboard$(4, 1) = "wrook": chessboard$(1, 1) = ""
        IF playerColor$ = "w" AND whiteSmallCastling = 1 THEN chessboard$(6, 1) = "wrook": chessboard$(8, 1) = ""
        IF playerColor$ = "b" AND blackBigCastling = 1 THEN chessboard$(4, 8) = "brook": chessboard$(1, 8) = ""
        IF playerColor$ = "b" AND blackSmallCastling = 1 THEN chessboard$(6, 8) = "brook": chessboard$(8, 8) = ""

        'Check for pawn promotion
        CALL PawnPromotion

        'En passant happened?
        IF enPassantHappened = 1 THEN
            IF enPassantRank = 3 THEN chessboard$(finishingColumn, 4) = ""
            IF enPassantRank = 6 THEN chessboard$(finishingColumn, 5) = ""
        END IF

        'En passant possible?
        enPassantColumn = 0
        enPassantRank = 0
        IF startingColumn = finishingColumn AND startingRank = 2 AND finishingRank = 4 AND MovingPiece$ = "wpawn" THEN
            enPassantColumn = finishingColumn
            enPassantRank = 3
        ELSEIF startingColumn = finishingColumn AND startingRank = 7 AND finishingRank = 5 AND MovingPiece$ = "bpawn" THEN
            enPassantColumn = finishingColumn
            enPassantRank = 6
        END IF

        CLS
        CALL drawBoard

        'Increase move number of the game
        IF playerColor$ = "w" THEN MoveNumber = MoveNumber + 1

        'Time for the computer to think now...
        IF playerColor$ = "b" THEN whichColorPlays$ = "White" '14/3/2021
        IF playerColor$ = "w" THEN whichColorPlays$ = "Black" '14/3/2021
        LOCATE 12, 1: PRINT "Huo Chess - HUOC"
        LOCATE 13, 1: PRINT "Thinking..."
        whoPlays$ = "HY"
        CALL computerMove

    ELSE

        LOCATE 12, 1: PRINT "Invalid move - Please try again"
        LOCATE 13, 1: PRINT "Press any key to continue"
        DO: LOOP UNTIL INKEY$ <> ""
        LOCATE 12, 1: PRINT "                               "
        LOCATE 13, 1: PRINT "                               "
        LOCATE 12, 1: PRINT "Huo Chess - HUOC"
        CALL PlayerMove

    END IF

END SUB


SUB computerMove

    'Initialize variables
    Move = 1
    bestPositionScore = 0
    bestStartingRank = 0
    bestStartingColumn = 0
    bestFinishingRank = 0
    bestFinishingColumn = 0
    IF playerColor$ = "w" THEN bestPositionScore = 999
    IF playerColor$ = "b" THEN bestPositionScore = -999
    'MinMax
    foundMove = 0
    NodeLevel_0_count = 1
    NodeLevel_1_count = 1
    NodeLevel_2_count = 1
    NodeLevel_3_count = 1
    NodeLevel_4_count = 1
    'Check
    whiteCheck = 0
    blackCheck = 0
    'En Passant
    enPassantHappened = 0
    MateFound = 0 '14/3/2021
    PatFound = 0 '14/3/2021
    bestStartingRankMate = 0 '14/3/2021
    bestStartingColumnMate = 0 '14/3/2021
    bestFinishingRankMate = 0 '14/3/2021
    bestFinishingColumnMate = 0 '14/3/2021

    'Check the Check
    IF playerColor$ = "b" THEN CALL checkWhiteCheck(chessboard$())
    IF playerColor$ = "w" THEN CALL checkBlackCheck(chessboard$())
    'PRINT "PlayerMove: blackCheck = " + STR$(blackCheck): INPUT aa$
    IF whiteCheck = 1 OR blackCheck = 1 THEN LOCATE 12, 1: PRINT "Check!            ": LOCATE 13, 1: PRINT "Press Enter": DO: LOOP UNTIL INKEY$ <> "": LOCATE 12, 1: PRINT "                 ": LOCATE 13, 1: PRINT "           "

    IF computerLogs$ = "y" THEN debugMode = 1 ELSE debugMode = 0

    IF debugMode = 1 THEN PRINT "chessboard$(1,1) = " + chessboard$(1, 1)
    IF debugMode = 1 THEN PRINT "MID$(chessboard$(1, 1), 1, 1) = " + MID$(chessboard$(1, 1), 1, 1)

    ' ------------------- OPENING (start) -------------------

    'Search for the position
    FileNum = 0
    positionFile$ = ""
    foundOpening = 0
    newLine$ = ""

    DO
        FileNum = FileNum + 1
        openingFile$ = "Opening" + LTRIM$(STR$(FileNum)) + ".txt"
        IF _FILEEXISTS(openingFile$) THEN
            verifyPosition = 1
            CLOSE #4
            OPEN openingFile$ FOR INPUT AS #4
            FOR i = 1 TO 8
                FOR j = 1 TO 8
                    LINE INPUT #4, newLine$
                    IF CHR$(34) + chessboard$(i, j) + CHR$(34) <> newLine$ THEN verifyPosition = 0
                NEXT j
            NEXT i
            'If position is found, store the file and read the suggested move!
            IF verifyPosition = 1 THEN
                positionFile$ = openingFile$
                foundOpening = 1
                'Read Suggested Move line
                LINE INPUT #4, newLine$
                'Read the coordinates of the suggested move
                LINE INPUT #4, newLine$
                bestStartingColumn = VAL(newLine$)
                LINE INPUT #4, newLine$
                bestStartingRank = VAL(newLine$)
                LINE INPUT #4, newLine$
                bestFinishingColumn = VAL(newLine$)
                LINE INPUT #4, newLine$
                bestFinishingRank = VAL(newLine$)
            END IF
        ELSE
            positionFile$ = "Not found"
        END IF
    LOOP WHILE positionFile$ = ""

    IF foundOpening = 1 THEN
        'PRINT "Found position in file: " + positionFile$
        'PRINT "Suggested move: " + STR$(openingStartColumn) + STR$(openingStartRank) + " -> " + STR$(openingFinishColumn) + STR$(openingFinishRank)
        'INPUT H$
        GOTO bestMoveSection
    END IF

    ' ------------------- OPENING (end) -------------------

    'Scan the chessboard...
    FOR i = 1 TO 8
        FOR j = 1 TO 8

            'If you find a piece of the computer...
            IF ((MID$(chessboard$(i, j), 1, 1) = "w" AND playerColor$ = "b") OR (MID$(chessboard$(i, j), 1, 1) = "b" AND playerColor$ = "w")) THEN

                IF debugMode = 1 THEN PRINT "Inside Computer Mode - Checkpoint A"

                'Scan all possible destination squares...
                FOR ii = 1 TO 8
                    FOR jj = 1 TO 8

                        startingColumn = i
                        startingRank = j
                        finishingColumn = ii
                        finishingRank = jj

                        MovingPiece$ = chessboard$(i, j)
                        ProsorinoKommati$ = chessboard$(ii, jj)

                        'Check legality of the move entered
                        CalledFromCheckCheck = 0 '14/3/2021
                        CALL ElegxosNomimotitas(chessboard$(), 0, startingColumn, startingRank, finishingColumn, finishingRank, MovingPiece$)

                        ' ------------------ Check the Check! START ------------------

                        'Temporarily do the move
                        chessboard$(finishingColumn, finishingRank) = chessboard$(startingColumn, startingRank)
                        chessboard$(startingColumn, startingRank) = ""

                        'Trela = 0
                        'IF Nomimotita = 1 THEN PRINT "Check A: whiteCheck = " + STR$(whiteCheck) + " , Nomimotita = " + STR$(Nomimotita): Trela = 1: INPUT A$

                        'Check the check
                        IF playerColor$ = "b" AND Nomimotita = 1 THEN
                            whoPlays$ = "Human"
                            CALL checkWhiteCheck(chessboard$())
                            'Restore Nomimotita! (because it is 'broken' in the checkCheck function
                            Nomimotita = 1
                            IF whiteCheck = 1 THEN Nomimotita = 0
                            'IF Trela = 1 THEN PRINT "Check B: whiteCheck = " + STR$(whiteCheck) + " , Nomimotita = " + STR$(Nomimotita): INPUT A$
                            whoPlays$ = "HY"
                        END IF

                        IF playerColor$ = "w" AND Nomimotita = 1 THEN
                            whoPlays$ = "Human"
                            CALL checkBlackCheck(chessboard$())
                            'Restore Nomimotita! (because it is 'broken' in the checkCheck function
                            Nomimotita = 1
                            IF blackCheck = 1 THEN Nomimotita = 0
                            whoPlays$ = "HY"
                        END IF

                        'Undo the move
                        chessboard$(startingColumn, startingRank) = MovingPiece$
                        chessboard$(finishingColumn, finishingRank) = ProsorinoKommati$

                        ' ------------------ Check the Check! END ------------------

                        IF debugMode = 1 THEN
                            PRINT ""
                            PRINT "NEW MOVE ANALYZED: " + STR$(startingColumn) + STR$(startingRank) + " -> " + STR$(finishingColumn) + STR$(finishingRank)
                            PRINT "Legality of the move analyzed: " + STR$(Nomimotita)
                        END IF

                        'If move is legal, then do the move and present it in the chessbooard
                        IF Nomimotita = 1 THEN

                            '-------------- MinMax --------------
                            'Important note: All dimensions in the tables are +1 compared to the Huo Chess in C#! (tables start from 1 here)

                            NodesAnalysis0(NodeLevel_0_count, 3) = startingColumn
                            NodesAnalysis0(NodeLevel_0_count, 4) = finishingColumn
                            NodesAnalysis0(NodeLevel_0_count, 5) = startingRank
                            NodesAnalysis0(NodeLevel_0_count, 6) = finishingRank

                            'If first move found, then store it (This is useless)
                            IF foundMove = 0 THEN
                                'NodesAnalysis0(NodeLevel_0_count, 3) = startingColumn
                                'NodesAnalysis0(NodeLevel_0_count, 4) = finishingColumn
                                'NodesAnalysis0(NodeLevel_0_count, 5) = startingRank
                                'NodesAnalysis0(NodeLevel_0_count, 6) = finishingRank
                                'PRINT "startingColumn = " + STR$(startingColumn)
                                'PRINT "finishingColumn = " + STR$(finishingColumn)
                                'PRINT "startingRank = " + STR$(startingRank)
                                'PRINT "finishingRank = " + STR$(finishingRank)
                                'INPUT A$
                                foundMove = 1
                            END IF

                            'Do the move
                            chessboard$(finishingColumn, finishingRank) = chessboard$(startingColumn, startingRank)
                            chessboard$(startingColumn, startingRank) = ""

                            'Count the score of the move
                            CALL countScore

                            '-------------- MinMax --------------
                            'Store scores
                            NodesAnalysis0(NodeLevel_0_count, 1) = positionScore
                            ' Store parents
                            NodesAnalysis0(NodeLevel_0_count, 2) = 0

                            IF Move = thinkingDepth THEN
                                'If the score is better than the existing best score, then this is the best move now (and the best score)
                                IF ((playerColor$ = "b" AND positionScore >= bestPositionScore) OR (playerColor$ = "w" AND positionScore <= bestPositionScore)) THEN
                                    bestStartingRank = startingRank
                                    bestStartingColumn = startingColumn
                                    bestFinishingRank = finishingRank
                                    bestFinishingColumn = finishingColumn
                                    bestPositionScore = positionScore
                                END IF
                            END IF

                            IF Move < thinkingDepth THEN
                                Move = Move + 1
                                IF playerColor$ = "b" THEN whichColorPlays$ = "Black" '14/3/2021
                                IF playerColor$ = "w" THEN whichColorPlays$ = "White" '14/3/2021
                                CALL HumanMove1(chessboard$())
                            END IF

                            'Restore the color playing (14/3/2021)
                            IF playerColor$ = "b" THEN whichColorPlays$ = "White" '14/3/2021
                            IF playerColor$ = "w" THEN whichColorPlays$ = "Black" '14/3/2021

                            'Undo the move
                            chessboard$(startingColumn, startingRank) = MovingPiece$
                            chessboard$(finishingColumn, finishingRank) = ProsorinoKommati$

                            'If pat (= stalemate in Greek) found, then nullify the score of the move (14/3/2021)
                            IF PatFound = 1 THEN
                                NodesAnalysis0(NodeLevel_0_count, 1) = 0
                            END IF

                            '-------------- MinMax --------------
                            'Increase node count
                            NodeLevel_0_count = NodeLevel_0_count + 1

                        END IF

                    NEXT jj
                NEXT ii

            END IF

        NEXT j
    NEXT i

    IF debugMode = 1 THEN
        PRINT "bestStartingRank = " + STR$(bestStartingRank)
        PRINT "bestStartingColumn = " + STR$(bestStartingColumn)
        PRINT "bestFinishingRank = " + STR$(bestFinishingRank)
        PRINT "bestFinishingColumn = " + STR$(bestFinishingColumn)
    END IF

    '-------------- MinMax --------------
    CALL MinMax

    'If mate found, then go for it! (14/3/2021)
    IF (MateFound = 1) THEN
        bestStartingRank = bestStartingRankMate
        bestStartingColumn = bestStartingColumnMate
        bestFinishingRank = bestFinishingRankMate
        bestFinishingColumn = bestFinishingColumnMate
    END IF

    'No move found? Then resign! Else, make the move!

    IF bestFinishingColumn = 0 THEN

        LOCATE 12, 1: PRINT "I resign!   "

    ELSE

        'En passant test
        'IF enPassantTest = 0 THEN
        '    bestStartingColumn = 5: bestStartingRank = 2
        '    bestFinishingColumn = 5: bestFinishingRank = 4
        '    enPassantTest = 1
        'END IF

        bestMoveSection:

        'Do the best move found
        chessboard$(bestFinishingColumn, bestFinishingRank) = chessboard$(bestStartingColumn, bestStartingRank)
        chessboard$(bestStartingColumn, bestStartingRank) = ""

        'Check for pawn promotion
        CALL PawnPromotion

        'En passant happened?
        IF (finishColumn = enPassantColumn) AND (finishRank = enPassantRank) THEN enPassantHappened = 1 ELSE enPassantHappened = 0

        'En passant happened?
        IF enPassantHappened = 1 THEN
            IF enPassantRank = 3 THEN chessboard$(finishingColumn, 4) = ""
            IF enPassantRank = 6 THEN chessboard$(finishingColumn, 5) = ""
        END IF

        'En passant possible?
        enPassantColumn = 0
        enPassantRank = 0
        IF bestStartingColumn = bestFinishingColumn AND bestStartingRank = 2 AND bestFinishingRank = 4 AND chessboard$(bestFinishingColumn, bestFinishingRank) = "wpawn" THEN
            enPassantColumn = bestFinishingColumn
            enPassantRank = 3
        ELSEIF bestStartingColumn = bestFinishingColumn AND bestStartingRank = 7 AND bestFinishingRank = 5 AND chessboard$(bestFinishingColumn, bestFinishingRank) = "bpawn" THEN
            enPassantColumn = bestFinishingColumn
            enPassantRank = 6
        END IF

        CLS
        CALL drawBoard

        'Increase move number of the game
        IF playerColor$ = "b" THEN MoveNumber = MoveNumber + 1

        SELECT CASE bestStartingColumn
            CASE 1
                startingColumnText$ = "a"
            CASE 2
                startingColumnText$ = "b"
            CASE 3
                startingColumnText$ = "c"
            CASE 4
                startingColumnText$ = "d"
            CASE 5
                startingColumnText$ = "e"
            CASE 6
                startingColumnText$ = "f"
            CASE 7
                startingColumnText$ = "g"
            CASE 8
                startingColumnText$ = "h"
        END SELECT

        SELECT CASE bestFinishingColumn
            CASE 1
                finishingColumnText$ = "a"
            CASE 2
                finishingColumnText$ = "b"
            CASE 3
                finishingColumnText$ = "c"
            CASE 4
                finishingColumnText$ = "d"
            CASE 5
                finishingColumnText$ = "e"
            CASE 6
                finishingColumnText$ = "f"
            CASE 7
                finishingColumnText$ = "g"
            CASE 8
                finishingColumnText$ = "h"
        END SELECT

        LOCATE 12, 1: PRINT "My move: " + startingColumnText$ + STR$(bestStartingRank) + " -> " + finishingColumnText$ + STR$(bestFinishingRank)

        'Time for the human to play now...
        whoPlays$ = "Human"
        IF playerColor$ = "b" THEN whichColorPlays$ = "Black" '14/3/2021
        IF playerColor$ = "w" THEN whichColorPlays$ = "White" '14/3/2021
        CALL PlayerMove

    END IF

END SUB

'-----------------------------------------------------------------------------------------------------

SUB initialPosition

    chessboard$(1, 1) = "wrook": chessboard$(1, 2) = "wpawn"
    chessboard$(2, 1) = "wknight": chessboard$(2, 2) = "wpawn"
    chessboard$(3, 1) = "wbishop": chessboard$(3, 2) = "wpawn"
    chessboard$(4, 1) = "wqueen": chessboard$(4, 2) = "wpawn"
    chessboard$(5, 1) = "wking": chessboard$(5, 2) = "wpawn"
    chessboard$(6, 1) = "wbishop": chessboard$(6, 2) = "wpawn"
    chessboard$(7, 1) = "wknight": chessboard$(7, 2) = "wpawn"
    chessboard$(8, 1) = "wrook": chessboard$(8, 2) = "wpawn"

    chessboard$(1, 7) = "bpawn": chessboard$(1, 8) = "brook"
    chessboard$(2, 7) = "bpawn": chessboard$(2, 8) = "bknight"
    chessboard$(3, 7) = "bpawn": chessboard$(3, 8) = "bbishop"
    chessboard$(4, 7) = "bpawn": chessboard$(4, 8) = "bqueen"
    chessboard$(5, 7) = "bpawn": chessboard$(5, 8) = "bking"
    chessboard$(6, 7) = "bpawn": chessboard$(6, 8) = "bbishop"
    chessboard$(7, 7) = "bpawn": chessboard$(7, 8) = "bknight"
    chessboard$(8, 7) = "bpawn": chessboard$(8, 8) = "brook"

    'Test

    'FOR q = 1 TO 8
    '  FOR w = 1 TO 8
    '    chessboard$(q, w) = ""
    '  NEXT w
    'NEXT q

    'chessboard$(4, 4) = "wbishop"
    'chessboard$(5, 5) = "bbishop"
    'chessboard$(1, 1) = "wrook"
    'chessboard$(1, 8) = "brook"
    'chessboard$(2, 2) = "wpawn"

    '---------- TEST ----------

    'chessboard$(1, 1) = "wrook": chessboard$(1, 2) = "wpawn"
    'chessboard$(2, 1) = "wknight": chessboard$(2, 2) = "bpawn"
    'chessboard$(3, 1) = "": chessboard$(3, 2) = "wpawn"
    'chessboard$(4, 1) = "": chessboard$(4, 2) = "wpawn"
    'chessboard$(5, 1) = "wking": chessboard$(5, 2) = ""
    'chessboard$(6, 1) = "": chessboard$(6, 2) = "wpawn"
    'chessboard$(7, 1) = "wknight": chessboard$(7, 2) = "wpawn"
    'chessboard$(8, 1) = "wrook": chessboard$(8, 2) = ""

    'chessboard$(1, 7) = "": chessboard$(1, 8) = "brook"
    'chessboard$(2, 7) = "wbishop": chessboard$(2, 8) = "bknight"
    'chessboard$(3, 7) = "bpawn": chessboard$(3, 8) = ""
    'chessboard$(4, 7) = "bpawn": chessboard$(4, 8) = "bqueen"
    'chessboard$(5, 7) = "bpawn": chessboard$(5, 8) = "bking"
    'chessboard$(6, 7) = "bpawn": chessboard$(6, 8) = "bbishop"
    'chessboard$(7, 7) = "bpawn": chessboard$(7, 8) = "bknight"
    'chessboard$(8, 7) = "bpawn": chessboard$(8, 8) = "brook"

    'chessboard$(4, 4) = "wpawn"
    'chessboard$(2, 4) = "wbishop"
    'chessboard$(6, 4) = "wqueen"
    'chessboard$(7, 6) = "bbishop"

    '---------- CASTLING TEST ----------

    'chessboard$(1, 1) = "wrook": chessboard$(1, 2) = "wpawn"
    'chessboard$(3, 3) = "wknight": chessboard$(2, 2) = "wpawn"
    'chessboard$(6, 4) = "wbishop": chessboard$(3, 2) = "wpawn"
    'chessboard$(4, 2) = "wqueen": chessboard$(4, 3) = "wpawn"
    'chessboard$(5, 1) = "wking": chessboard$(5, 5) = "wpawn"
    'chessboard$(3, 4) = "wbishop": chessboard$(6, 2) = "wpawn"
    'chessboard$(6, 3) = "wknight": chessboard$(7, 2) = "wpawn"
    'chessboard$(8, 1) = "wrook": chessboard$(8, 2) = "wpawn"

    'chessboard$(1, 7) = "bpawn": chessboard$(1, 8) = "brook"
    'chessboard$(2, 6) = "bpawn": chessboard$(3, 6) = "bknight"
    'chessboard$(3, 7) = "bpawn": chessboard$(1, 4) = "bbishop"
    'chessboard$(4, 5) = "bpawn": chessboard$(4, 7) = "bqueen"
    'chessboard$(5, 6) = "bpawn": chessboard$(5, 8) = "bking"
    'chessboard$(6, 7) = "bpawn": chessboard$(5, 7) = "bbishop"
    'chessboard$(7, 7) = "bpawn": chessboard$(8, 6) = "bknight"
    'chessboard$(8, 7) = "bpawn": chessboard$(8, 8) = "brook"

    '---------- CHECK TEST ----------

    'chessboard$(1, 1) = "wrook": chessboard$(1, 2) = "wpawn"
    'chessboard$(2, 5) = "wknight": chessboard$(2, 2) = "wpawn"
    'chessboard$(6, 4) = "wbishop": chessboard$(3, 2) = "wpawn"
    'chessboard$(4, 2) = "wqueen": chessboard$(4, 3) = "wpawn"
    'chessboard$(5, 1) = "wking": chessboard$(5, 5) = "wpawn"
    'chessboard$(3, 4) = "wbishop": chessboard$(6, 2) = "wpawn"
    'chessboard$(6, 3) = "wknight": chessboard$(7, 2) = "wpawn"
    'chessboard$(8, 1) = "wrook": chessboard$(8, 2) = "wpawn"

    'chessboard$(1, 7) = "bpawn": chessboard$(1, 8) = "brook"
    'chessboard$(2, 6) = "bpawn": chessboard$(3, 6) = "bknight"
    'chessboard$(3, 7) = "bpawn": chessboard$(1, 4) = "bbishop"
    'chessboard$(4, 5) = "bpawn": chessboard$(4, 7) = "bqueen"
    'chessboard$(5, 6) = "bpawn": chessboard$(5, 8) = "bking"
    'chessboard$(6, 7) = "bpawn": chessboard$(5, 7) = "bbishop"
    'chessboard$(7, 7) = "bpawn": chessboard$(8, 4) = "bknight"
    'chessboard$(8, 7) = "bpawn": chessboard$(8, 8) = "brook"

    '---------- EN PASSANT TEST ----------

    'chessboard$(1, 1) = "wrook": chessboard$(1, 2) = "wpawn"
    'chessboard$(2, 1) = "wknight": chessboard$(2, 2) = "wpawn"
    'chessboard$(3, 1) = "wbishop": chessboard$(3, 4) = "wpawn"
    'chessboard$(4, 1) = "wqueen": chessboard$(4, 2) = "wpawn"
    'chessboard$(5, 1) = "wking": chessboard$(5, 2) = "wpawn"
    'chessboard$(6, 1) = "wbishop": chessboard$(6, 2) = "wpawn"
    'chessboard$(7, 1) = "wknight": chessboard$(7, 5) = "wpawn"
    'chessboard$(8, 1) = "wrook": chessboard$(8, 2) = "wpawn"

    'chessboard$(1, 7) = "bpawn": chessboard$(1, 8) = "brook"
    'chessboard$(2, 7) = "bpawn": chessboard$(2, 8) = "bknight"
    'chessboard$(3, 7) = "bpawn": chessboard$(3, 8) = "bbishop"
    'chessboard$(4, 4) = "bpawn": chessboard$(4, 8) = "bqueen"
    'chessboard$(5, 7) = "bpawn": chessboard$(5, 8) = "bking"
    'chessboard$(6, 7) = "bpawn": chessboard$(6, 8) = "bbishop"
    'chessboard$(7, 7) = "bpawn": chessboard$(7, 8) = "bknight"
    'chessboard$(8, 5) = "bpawn": chessboard$(8, 8) = "brook"

END SUB

' -------------------------------------------------------------------------------------------------------

SUB drawBoard

    sqcolor$ = "" 'Square color
    piece$ = "" 'Piece to be printed
    pfcolor = 0 'Piece front color
    pbcolor = 1 'Piece back color

    MT$ = CHR$(219)
    SQ$ = MT$ + MT$ + MT$

    'CLS 0
    SCREEN 0
    'COLOR 6
    'LINE (0, 0)-(30, 30), 0, BF

    LOCATE 1, 1
    PRINT "HUO Chess (HUOC) by Spiros (h uo) Kakos - Alpha version"

    FOR i = 1 TO 8
        FOR j = 1 TO 8

            IF (i + j) MOD 2 = 0 THEN
                sqcolor$ = "b"
            ELSEIF (i + j) MOD 2 <> 0 THEN
                sqcolor$ = "w"
            END IF

            'Columns are the first number inside the parenthesis and
            'because we start drawing the board from upside-up, we
            'must apply this (9 - i) to draw the board correctly

            'Print the square
            LOCATE 2 + (9 - i), 1 + (j - 1) * 3
            IF sqcolor$ = "w" THEN
                COLOR 7, 0
            ELSEIF sqcolor$ = "b" THEN
                COLOR 0, 7
            END IF
            PRINT SQ$

            'Determine the color of the piece to print
            IF LEFT$(chessboard$(j, i), 1) = "w" AND sqcolor$ = "w" THEN
                pfcolor = 15
                pbcolor = 7
            ELSEIF LEFT$(chessboard$(j, i), 1) = "w" AND sqcolor$ = "b" THEN
                pfcolor = 15
                pbcolor = 0
            ELSEIF LEFT$(chessboard$(j, i), 1) = "b" AND sqcolor$ = "w" THEN
                pfcolor = 5
                pbcolor = 7
            ELSEIF LEFT$(chessboard$(j, i), 1) = "b" AND sqcolor$ = "b" THEN
                pfcolor = 5
                pbcolor = 0
            END IF

            SELECT CASE chessboard$(j, i)

                CASE "wking"
                    piece$ = "K"
                CASE "wqueen"
                    piece$ = "Q"
                CASE "wrook"
                    piece$ = "R"
                CASE "wbishop"
                    piece$ = "B"
                CASE "wknight"
                    piece$ = "N"
                CASE "wpawn"
                    piece$ = "o"
                CASE "bking"
                    piece$ = "K"
                CASE "bqueen"
                    piece$ = "Q"
                CASE "brook"
                    piece$ = "R"
                CASE "bbishop"
                    piece$ = "B"
                CASE "bknight"
                    piece$ = "N"
                CASE "bpawn"
                    piece$ = "o"
                CASE ""
                    piece$ = ""

            END SELECT

            'Print the piece
            LOCATE 2 + (9 - i), 2 + (j - 1) * 3
            COLOR pfcolor, pbcolor
            PRINT piece$

        NEXT j
    NEXT i

    'Restore color of screen and text
    COLOR 7, 0

    'Restore cursor
    LOCATE 13, 1

END SUB

' -------------------------------------------------------------------------------------------------------

SUB ElegxosNomimotitas (ENSkakiera() AS STRING, checkForDanger AS INTEGER, startColumn AS INTEGER, startRank AS INTEGER, finishColumn AS INTEGER, finishRank AS INTEGER, MovingPieceEN AS STRING)

    'Some GREEK: Skakiera in Greek means "chessboard". Nomimotita in Greek means "legality".
    'This SUB checks the legality of the moves enetered by the player or thought by the computer

    DIM ProsorinoKommatiEN AS STRING
    DIM NomimotitaEN

    NomimotitaEN = 1 'Set legality (= Nomimotita in Greek) to TRUE. If a problem is found then it will be set to FALSE.

    IF (debugMode = 1) THEN
        PRINT ""
        PRINT "--------------- DEBUG MESSAGE ---------------"
        PRINT "ElegxosNomimotitas CALLED"
        PRINT ""
        PRINT "Start column: " + STR$(startColumn)
        PRINT "Start rank  : " + STR$(startRank)
        PRINT "End column  : " + STR$(finishColumn)
        PRINT "End rank    : " + STR$(finishRank)
        PRINT ""
        PRINT "Moving piece: " + MovingPieceEN$
        PRINT "ENSkakiera(1,1) = " + ENSkakiera(1, 1)
        PRINT "ENSkakiera(1,2) = " + ENSkakiera(1, 2)
        PRINT ""
        PRINT "playerColor$ = " + playerColor$
        PRINT "---------------------------------------------"
        PRINT ""
        INPUT a$
    END IF

    'If player moves a different colour piece then move is illegal
    IF whoPlays$ = "Human" THEN
        IF MID$(playerColor$, 1, 1) <> MID$(ENSkakiera$(startColumn, startRank), 1, 1) THEN NomimotitaEN = 0
    END IF
    IF whoPlays$ = "HY" THEN
        IF MID$(playerColor$, 1, 1) = MID$(ENSkakiera$(startColumn, startRank), 1, 1) THEN NomimotitaEN = 0
    END IF

    ' ------------------------------------ ROOK ------------------------------------
    IF (MovingPieceEN$ = "wrook" OR MovingPieceEN$ = "brook") THEN

        IF debugMode = 1 THEN PRINT "Nomimotita = " + STR$(NomimotitaEN)

        'Check correctness of move (Rook only moves in lines)

        IF ((startColumn <> finishColumn) AND (startRank <> finishRank)) THEN NomimotitaEN = 0

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Checkpoint ROOK-0"

        'Check if the Rook moves beyond the limits of the chessboard

        IF ((finishColumn < 1) OR (finishRank < 1)) THEN NomimotitaEN = 0
        IF ((finishColumn > 8) OR (finishRank > 8)) THEN NomimotitaEN = 0

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Checkpoint ROOK-1"

        'Check if another piece is between the current and the target square

        'Horizontal movement

        IF (startColumn > finishColumn) AND (startRank = finishRank) THEN
            FOR J = startColumn TO finishColumn STEP -1
                IF (J <> startColumn) AND (J <> finishColumn) AND ENSkakiera(J, startRank) <> "" THEN NomimotitaEN = 0
            NEXT J
        END IF

        IF (startColumn < finishColumn) AND (startRank = finishRank) THEN
            FOR J = startColumn TO finishColumn
                IF (J <> startColumn) AND (J <> finishColumn) AND ENSkakiera(J, startRank) <> "" THEN NomimotitaEN = 0
            NEXT J
        END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Checkpoint ROOK-2"

        'Vertical movement

        IF (startColumn = finishColumn) AND (startRank > finishRank) THEN
            FOR J = startRank TO finishRank STEP -1
                IF (J <> startRank) AND (J <> finishRank) AND ENSkakiera(startColumn, J) <> "" THEN NomimotitaEN = 0
            NEXT J
        END IF

        IF (startColumn = finishColumn) AND (startRank < finishRank) THEN
            FOR J = startRank TO finishRank
                IF (J <> startRank) AND (J <> finishRank) AND ENSkakiera(startColumn, J) <> "" THEN NomimotitaEN = 0
            NEXT J
        END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Checkpoint ROOK-3"

        'If the start square is the same as the destination...
        IF startColumn = finishColumn AND startRank = finishRank THEN NomimotitaEN = 0

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Checkpoint ROOK-4"

        'Check if a piece of the same colour is at the destination square
        IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = MID$(ENSkakiera$(startColumn, startRank), 1, 1) THEN NomimotitaEN = 0

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Checkpoint ROOK-5": 'INPUT a$

    END IF

    ' ------------------------------------ BISHOP ------------------------------------

    IF (MovingPieceEN$ = "wbishop" OR MovingPieceEN$ = "bbishop") THEN

        'Check correctness of move (Bishop only moves in diagonals)

        IF ((startRank = finishRank) OR (startColumn = finishColumn)) THEN NomimotitaEN = 0
        IF (ABS(startColumn - finishColumn) <> ABS(startRank - finishRank)) THEN NomimotitaEN = 0

        'IF MovingPieceEN$ = "wbishop" AND startColumn = 2 AND startRank = 4 AND finishColumn = 5 AND finishRank = 7 THEN
        '    PRINT "Checkpoint 1 - Nomimotita = " + STR$(NomimotitaEN)
        '    INPUT C$
        'END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Bishop - Checkpoint A"

        'Check if the piece moves beyond the limits of the chessboard

        IF ((finishColumn < 1) OR (finishRank < 1)) THEN NomimotitaEN = 0
        IF ((finishColumn > 8) OR (finishRank > 8)) THEN NomimotitaEN = 0

        'IF MovingPieceEN$ = "wbishop" AND startColumn = 2 AND startRank = 4 AND finishColumn = 5 AND finishRank = 7 THEN
        '    PRINT "Checkpoint 2 - Nomimotita = " + STR$(NomimotitaEN)
        '    INPUT C$
        'END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Bishop - Checkpoint B"

        'Check if another piece is between the current and the target square

        'Move down-left
        IF (finishColumn < startColumn) AND (finishRank < startRank) THEN
            FOR I = 1 TO 7
                IF (startColumn - I) > 0 AND (startRank - I) > 0 THEN
                    IF (startColumn - I) > finishColumn AND (startRank - I) > finishRank AND ENSkakiera(startColumn - I, startRank - I) <> "" THEN NomimotitaEN = 0
                END IF
            NEXT I
        END IF

        'Move up-left
        IF (finishColumn < startColumn) AND (finishRank > startRank) THEN
            FOR I = 1 TO 7
                IF (startColumn - I) > 0 AND (startRank + I) < 9 THEN
                    IF (startColumn - I) > finishColumn AND (startRank + I) < finishRank AND ENSkakiera(startColumn - I, startRank + I) <> "" THEN NomimotitaEN = 0
                END IF
            NEXT I
        END IF

        'IF MovingPieceEN$ = "wbishop" AND startColumn = 2 AND startRank = 4 AND finishColumn = 5 AND finishRank = 7 THEN
        '    PRINT "Checkpoint 3 - Nomimotita = " + STR$(NomimotitaEN)
        '    INPUT C$
        'END IF

        'Move up-right
        IF (finishColumn > startColumn) AND (finishRank > startRank) THEN
            FOR I = 1 TO 7
                IF (startColumn + I) < 9 AND (startRank + I) < 9 THEN
                    IF (startColumn + I) < finishColumn AND (startRank + I) < finishRank AND ENSkakiera(startColumn + I, startRank + I) <> "" THEN NomimotitaEN = 0

                    'IF MovingPieceEN$ = "wbishop" AND startColumn = 2 AND startRank = 4 AND finishColumn = 5 AND finishRank = 7 THEN
                    '    PRINT "Checkpoint 3.0 - Nomimotita = " + STR$(NomimotitaEN) + " (i = " + STR$(I) + ")"
                    '    INPUT C$
                    'END IF
                END IF
            NEXT I
        END IF

        'IF MovingPieceEN$ = "wbishop" AND startColumn = 2 AND startRank = 4 AND finishColumn = 5 AND finishRank = 7 THEN
        '    PRINT "Checkpoint 3.1 - Nomimotita = " + STR$(NomimotitaEN)
        '    INPUT C$
        'END IF

        'Move down-right
        IF (finishColumn > startColumn) AND (finishRank < startRank) THEN
            FOR I = 1 TO 7
                IF (startColumn + I) < 9 AND (startRank - I) > 0 THEN
                    IF (startColumn + I) < finishColumn AND (startRank - I) > finishRank AND ENSkakiera(startColumn + I, startRank - I) <> "" THEN NomimotitaEN = 0
                END IF
            NEXT I
        END IF

        'IF MovingPieceEN$ = "wbishop" AND startColumn = 2 AND startRank = 4 AND finishColumn = 5 AND finishRank = 7 THEN
        '    PRINT "Checkpoint 4 - Nomimotita = " + STR$(NomimotitaEN)
        '    INPUT C$
        'END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Bishop - Checkpoint C"

        'If the start square is the same as the destination...
        IF startColumn = finishColumn AND startRank = finishRank THEN NomimotitaEN = 0

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Bishop - Checkpoint D"

        'Check if a piece of the same colour is at the destination square
        IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = MID$(ENSkakiera$(startColumn, startRank), 1, 1) THEN NomimotitaEN = 0

        'IF MovingPieceEN$ = "wbishop" AND startColumn = 2 AND startRank = 4 AND finishColumn = 5 AND finishRank = 7 THEN
        '    PRINT "Checkpoint 5 - Nomimotita = " + STR$(NomimotitaEN)
        '    INPUT C$
        'END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Bishop - Checkpoint E": 'INPUT a$

    END IF

    ' ------------------------------------ QUEEN ------------------------------------

    IF (MovingPieceEN$ = "wqueen" OR MovingPieceEN$ = "bqueen") THEN

        'Check correctness of move (Queen moves in diagonals and in lines)
        'Different check depending on whether the queen moves in lines or not.
        'Checks are a combination of the above checks for Rook and Bishop.

        IF (startRank <> finishRank) AND (startColumn <> finishColumn) THEN
            IF (ABS(startColumn - finishColumn) <> ABS(startRank - finishRank)) THEN NomimotitaEN = 0
        END IF

        IF debugMode = 1 THEN PRINT "Queen - Entered check legality SUB": INPUT a$
        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Queen - Checkpoint Null"

        'Check if the piece moves beyond the limits of the chessboard

        IF ((finishColumn < 1) OR (finishRank < 1)) THEN NomimotitaEN = 0
        IF ((finishColumn > 8) OR (finishRank > 8)) THEN NomimotitaEN = 0

        'Check if another piece is between the current and the target square

        'Diagonal movement

        'Move down-left
        IF (finishColumn < startColumn) AND (finishRank < startRank) THEN
            FOR I = 1 TO 7
                IF (startColumn - I) > 0 AND (startRank - I) > 0 THEN
                    IF (startColumn - I) > finishColumn AND (startRank - I) > finishRank AND ENSkakiera(startColumn - I, startRank - I) <> "" THEN NomimotitaEN = 0
                END IF
            NEXT I
        END IF

        'Move up-left
        IF (finishColumn < startColumn) AND (finishRank > startRank) THEN
            FOR I = 1 TO 7
                IF (startColumn - I) > 0 AND (startRank + I) < 9 THEN
                    IF (startColumn - I) > finishColumn AND (startRank + I) < finishRank AND ENSkakiera(startColumn - I, startRank + I) <> "" THEN NomimotitaEN = 0
                END IF
            NEXT I
        END IF

        'Move up-right
        IF (finishColumn > startColumn) AND (finishRank > startRank) THEN
            FOR I = 1 TO 7
                IF (startColumn + I) < 9 AND (startRank + I) < 9 THEN
                    IF (startColumn + I) < finishColumn AND (startRank + I) < finishRank AND ENSkakiera(startColumn + I, startRank + I) <> "" THEN NomimotitaEN = 0
                END IF
            NEXT I
        END IF

        'Move down-right
        IF (finishColumn > startColumn) AND (finishRank < startRank) THEN
            FOR I = 1 TO 7
                IF (startColumn + I) < 9 AND (startRank - I) > 0 THEN
                    IF (startColumn + I) < finishColumn AND (startRank - I) > finishRank AND ENSkakiera(startColumn + I, startRank - I) <> "" THEN NomimotitaEN = 0
                END IF
            NEXT I
        END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Queen - Checkpoint 0"

        'Horizontal movement

        IF (startColumn > finishColumn) AND (startRank = finishRank) THEN
            FOR J = startColumn TO finishColumn STEP -1
                IF (J <> startColumn) AND (J <> finishColumn) AND ENSkakiera(J, startRank) <> "" THEN NomimotitaEN = 0
            NEXT J
        END IF

        IF (startColumn < finishColumn) AND (startRank = finishRank) THEN
            FOR J = startColumn TO finishColumn
                IF (J <> startColumn) AND (J <> finishColumn) AND ENSkakiera(J, startRank) <> "" THEN NomimotitaEN = 0
            NEXT J
        END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Queen - Checkpoint 1"
        IF debugMode = 1 THEN PRINT "startColumn = " + STR$(startColumn) + " - finishColumn = " + STR$(finishColumn)

        'Vertical movement

        IF (startColumn = finishColumn) AND (startRank > finishRank) THEN
            FOR J = startRank TO finishRank STEP -1
                IF (J <> startRank) AND (J <> finishRank) AND ENSkakiera(startColumn, J) <> "" THEN NomimotitaEN = 0
            NEXT J
        END IF

        IF (startColumn = finishColumn) AND (startRank < finishRank) THEN
            FOR J = startRank TO finishRank
                IF (J <> startRank) AND (J <> finishRank) AND ENSkakiera(startColumn, J) <> "" THEN NomimotitaEN = 0
            NEXT J
        END IF

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Queen - Checkpoint 2"

        'If the start square is the same as the destination...
        IF startColumn = finishColumn AND startRank = finishRank THEN NomimotitaEN = 0

        'Check if a piece of the same colour is at the destination square
        IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = MID$(ENSkakiera$(startColumn, startRank), 1, 1) THEN NomimotitaEN = 0

        IF debugMode = 1 AND NomimotitaEN = 0 THEN PRINT "Queen - Checkpoint 3": INPUT a$

    END IF

    ' ------------------------------------ KING ------------------------------------

    IF (MovingPieceEN$ = "wking" OR MovingPieceEN$ = "bking") THEN

        'Check correctness of move (King moves in diagonals and in lines, but only for one square)
        'Different check depending on whether the queen moves in lines or not.
        'Checks are the same as the checks for the Queen, with the addition of a check that King only moves one square.

        IF (startRank <> finishRank) AND (startColumn <> finishColumn) THEN
            IF (ABS(startColumn - finishColumn) <> ABS(startRank - finishRank)) THEN NomimotitaEN = 0
        END IF

        'Check if the King moves more than one square
        IF ABS(startColumn - finishColumn) > 1 OR ABS(startRank - finishRank) > 1 THEN NomimotitaEN = 0

        'Check if the piece moves beyond the limits of the chessboard

        IF ((finishColumn < 1) OR (finishRank < 1)) THEN NomimotitaEN = 0
        IF ((finishColumn > 8) OR (finishRank > 8)) THEN NomimotitaEN = 0

        'If the start square is the same as the destination...
        IF startColumn = finishColumn AND startRank = finishRank THEN NomimotitaEN = 0

        'Check if a piece of the same colour is at the destination square
        IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = MID$(ENSkakiera$(startColumn, startRank), 1, 1) THEN NomimotitaEN = 0

    END IF

    ' ------------------------------------ KNIGHT ------------------------------------

    IF (MovingPieceEN$ = "wknight" OR MovingPieceEN$ = "bknight") THEN

        NomimotitaEN = 0

        IF (finishColumn = startColumn + 2) AND (finishRank = startRank + 1) THEN NomimotitaEN = 1
        IF (finishColumn = startColumn + 2) AND (finishRank = startRank - 1) THEN NomimotitaEN = 1
        IF (finishColumn = startColumn + 1) AND (finishRank = startRank + 2) THEN NomimotitaEN = 1
        IF (finishColumn = startColumn + 1) AND (finishRank = startRank - 2) THEN NomimotitaEN = 1
        IF (finishColumn = startColumn - 1) AND (finishRank = startRank + 2) THEN NomimotitaEN = 1
        IF (finishColumn = startColumn - 1) AND (finishRank = startRank - 2) THEN NomimotitaEN = 1
        IF (finishColumn = startColumn - 2) AND (finishRank = startRank + 1) THEN NomimotitaEN = 1
        IF (finishColumn = startColumn - 2) AND (finishRank = startRank - 1) THEN NomimotitaEN = 1

        'Check if the piece moves beyond the limits of the chessboard

        IF ((finishColumn < 1) OR (finishRank < 1)) THEN NomimotitaEN = 0
        IF ((finishColumn > 8) OR (finishRank > 8)) THEN NomimotitaEN = 0

        'Check if a piece of the same colour is at the destination square
        IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = MID$(ENSkakiera$(startColumn, startRank), 1, 1) THEN NomimotitaEN = 0

        'If the start square is the same as the destination...
        IF startColumn = finishColumn AND startRank = finishRank THEN NomimotitaEN = 0

    END IF

    ' ------------------------------------ PAWN ------------------------------------

    IF (MovingPieceEN$ = "wpawn" OR MovingPieceEN$ = "bpawn") THEN

        NomimotitaEN = 0

        IF MovingPieceEN$ = "wpawn" THEN

            IF (finishColumn = startColumn) AND (finishRank = startRank + 1) THEN NomimotitaEN = 1

            IF (finishColumn = startColumn - 1) AND (finishRank = startRank + 1) THEN
                IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = "b" THEN NomimotitaEN = 1
                'En Passant
                IF finishColumn = enPassantColumn AND finishRank = enPassantRank THEN NomimotitaEN = 1
            END IF

            IF (finishColumn = startColumn + 1) AND (finishRank = startRank + 1) THEN
                IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = "b" THEN NomimotitaEN = 1
                'En Passant
                IF finishColumn = enPassantColumn AND finishRank = enPassantRank THEN NomimotitaEN = 1
            END IF

        END IF

        IF debugMode = 1 THEN PRINT "Pawn - Checkpoint Null: Nomimotita = " + STR$(NomimotitaEN)

        IF MovingPieceEN$ = "bpawn" THEN

            IF (finishColumn = startColumn) AND (finishRank = startRank - 1) THEN NomimotitaEN = 1

            IF (finishColumn = startColumn - 1) AND (finishRank = startRank - 1) THEN
                IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = "w" THEN NomimotitaEN = 1
                'En Passant
                IF finishColumn = enPassantColumn AND finishRank = enPassantRank THEN NomimotitaEN = 1
            END IF

            IF (finishColumn = startColumn + 1) AND (finishRank = startRank - 1) THEN
                IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = "w" THEN NomimotitaEN = 1
                'En Passant
                IF finishColumn = enPassantColumn AND finishRank = enPassantRank THEN NomimotitaEN = 1
            END IF

        END IF

        'Moving two squares
        IF MovingPieceEN$ = "wpawn" AND startRank = 2 AND finishRank = 4 AND startColumn = finishColumn AND ENSkakiera$(startColumn, 3) = "" AND ENSkakiera$(startColumn, 4) = "" THEN NomimotitaEN = 1
        IF MovingPieceEN$ = "bpawn" AND startRank = 7 AND finishRank = 5 AND startColumn = finishColumn AND ENSkakiera$(startColumn, 6) = "" AND ENSkakiera$(startColumn, 5) = "" THEN NomimotitaEN = 1

        IF debugMode = 1 THEN PRINT "Pawn - Checkpoint 1: Nomimotita = " + STR$(NomimotitaEN)

        'Check if the piece moves beyond the limits of the chessboard

        IF ((finishColumn < 1) OR (finishRank < 1)) THEN NomimotitaEN = 0
        IF ((finishColumn > 8) OR (finishRank > 8)) THEN NomimotitaEN = 0

        'Check if a piece of the same colour is at the destination square
        IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = MID$(ENSkakiera$(startColumn, startRank), 1, 1) THEN NomimotitaEN = 0

        IF debugMode = 1 THEN PRINT "Pawn - Checkpoint 2: Nomimotita = " + STR$(NomimotitaEN)

        'Check if a piece of any colour is at the destination square

        IF (finishColumn <> startColumn) THEN
            IF MovingPieceEN$ = "wpawn" AND MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = "w" THEN NomimotitaEN = 0
            IF MovingPieceEN$ = "bpawn" AND MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) = "b" THEN NomimotitaEN = 0
        END IF

        IF (finishColumn = startColumn) THEN
            IF MID$(ENSkakiera$(finishColumn, finishRank), 1, 1) <> "" THEN NomimotitaEN = 0
        END IF

        IF debugMode = 1 THEN PRINT "Pawn - Checkpoint 3: Nomimotita = " + NomimotitaEN$: INPUT a$

        'If the start square is the same as the destination...
        IF startColumn = finishColumn AND startRank = finishRank THEN NomimotitaEN = 0

    END IF

    '14/3/2021: Attempted to make the check for check to be done here centrally, but it failed.
    'The problem was probably that the checkWhiteCheck and checkBlackCheck functions also themselves call ElegxosNomimotitas function!
    'That is why I added the CalledFromCheckCheck variable that would indicate whether the ElegxosNomimotitas is called from the PlayerMove or the computerMove
    'function (where CalledFromCheckCheck would be 0) or from the checkWhiteCheck or checkBlackCheck functions (where CalledFromCheckCheck would be 1).
    'Did not complete it, it had problems. Just leaving a note here for the future...
    ' ------------------ Check the Check! START (14/3/2021) ------------------
    'IF ((NomimotitaEN = 1) AND (Move < 3) AND (CalledFromCheckCheck = 0)) THEN

    '    'Revert the whoPlays for the checking of the check
    '    IF whoPlays$ = "Human" THEN
    '        whoPlays$ = "HY"
    '    ELSEIF whoPlays$ = "HY" THEN
    '        whoPlays$ = "Human"
    '    END IF

    '    'Temporarily do the move
    '    ProsorinoKommatiEN$ = ENSkakiera$(finishColumn, finishRank)
    '    ENSkakiera$(finishColumn, finishRank) = ENSkakiera$(startColumn, startRank)
    '    ENSkakiera$(startColumn, startRank) = ""

    '    'Check the check
    '    IF whichColorPlays$ = "White" THEN CALL checkWhiteCheck(ENSkakiera$())
    '    IF whichColorPlays$ = "Black" THEN CALL checkBlackCheck(ENSkakiera$())

    '    'Restore Nomimotita! (because it is 'broken' in the checkCheck function)
    '    Nomimotita = 1

    '    IF whichColorPlays$ = "White" AND whiteCheck = 1 THEN Nomimotita = 0
    '    IF whichColorPlays$ = "Black" AND blackCheck = 1 THEN Nomimotita = 0

    '    'Undo the move
    '    ENSkakiera$(startColumn, startRank) = MovingPieceEN$
    '    ENSkakiera$(finishColumn, finishRank) = ProsorinoKommatiEN$

    '    'Revert the whoPlays back
    '    IF whoPlays$ = "Human" THEN
    '        whoPlays$ = "HY"
    '    ELSEIF whoPlays$ = "HY" THEN
    '        whoPlays$ = "Human"
    '    END IF

    'END IF
    ' ------------------ Check the Check! END (14/3/2021) ------------------

    IF (debugMode = 1) THEN
        PRINT ""
        PRINT "--------------- DEBUG MESSAGE ---------------"
        PRINT "startColumn = " + STR$(startColumn)
        PRINT "startRank = " + STR$(startRank)
        PRINT "finishColumn = " + STR$(finishColumn)
        PRINT "finishRank = " + STR$(finishRank)
        PRINT "ENSkakiera$(startColumn, startRank) = " + ENSkakiera$(startColumn, startRank)
        PRINT "ENSkakiera$(finishColumn, finishRank) = " + ENSkakiera$(finishColumn, finishRank)
        PRINT ""
        PRINT "NomimotitaEN = " + STR$(NomimotitaEN)
        PRINT "--------------- DEBUG MESSAGE ---------------"
        PRINT ""
        INPUT a$
    END IF

    Nomimotita = NomimotitaEN

END SUB


SUB countScore

    'v0.5: Multipled all scores by 10-factor (e.g. score of a bishop is now 30 instead of 3), so that I can include additional checks for the position score.
    '      Without doing that I could not add the quality checks I added, e.g. the IF chessboard$(4, 4) = "wpawn" THEN positionScore = positionScore + 0.1.
    '      Now the additional score checks can be added with integers, e.g. IF chessboard$(4, 4) = "wpawn" THEN positionScore = positionScore + 1 for the above example.
    '      If I wanted to do what using decimals, then all positionScore, bestPositionScore, NodesAnalysis0... NodesAnalysis4 variables and arrays should de defined as DOUBLE, but then we would have memory problems...

    positionScore = 0

    Score_Multiplier_White = 1
    Score_Multiplier_Black = 1

    'Locate the position of the kings...
    FOR I = 1 TO 8
        FOR J = 1 TO 8
            IF chessboard$(I, J) = "wking" THEN
                wkingPositionI = I
                wkingPositionJ = J
            END IF
            IF chessboard$(I, J) = "bking" THEN
                bkingPositionI = I
                bkingPositionJ = J
            END IF
        NEXT J
    NEXT I

    FOR I = 1 TO 8
        FOR J = 1 TO 8

            'IF chessboard$(I, J) = "wpawn" THEN positionScore = positionScore + 1
            'IF chessboard$(I, J) = "wrook" THEN positionScore = positionScore + 5
            'IF chessboard$(I, J) = "wknight" THEN positionScore = positionScore + 3
            'IF chessboard$(I, J) = "wbishop" THEN positionScore = positionScore + 3
            'IF chessboard$(I, J) = "wqueen" THEN positionScore = positionScore + 9
            'IF chessboard$(I, J) = "wking" THEN positionScore = positionScore + 100

            'IF chessboard$(I, J) = "bpawn" THEN positionScore = positionScore - 1
            'IF chessboard$(I, J) = "brook" THEN positionScore = positionScore - 5
            'IF chessboard$(I, J) = "bknight" THEN positionScore = positionScore - 3
            'IF chessboard$(I, J) = "bbishop" THEN positionScore = positionScore - 3
            'IF chessboard$(I, J) = "bqueen" THEN positionScore = positionScore - 9
            'IF chessboard$(I, J) = "bking" THEN positionScore = positionScore - 100

            IF chessboard$(I, J) = "wpawn" THEN
                positionScore = positionScore + 10
                'At the end, passed pawns are a good thing...
                IF (Move > 30) AND (J > 4) THEN
                    positionScore = positionScore + 1
                END IF
                IF (Move > 30) AND (J > 5) THEN
                    positionScore = positionScore + 10
                END IF
                IF (Move > 30) AND (J > 7) THEN
                    positionScore = positionScore + 90
                END IF
            END IF

            IF chessboard$(I, J) = "wrook" THEN positionScore = positionScore + 50

            IF chessboard$(I, J) = "wknight" THEN
                positionScore = positionScore + 30
                'At the end of the game, go close to the kings...
                IF Move > 30 AND (ABS(I - bkingPositionI) < 5 OR ABS(J - bkingPositionJ) < 5) THEN
                    positionScore = positionScore + 5
                END IF
            END IF

            IF chessboard$(I, J) = "wbishop" THEN positionScore = positionScore + 30

            IF chessboard$(I, J) = "wqueen" THEN positionScore = positionScore + 90

            IF chessboard$(I, J) = "wking" THEN positionScore = positionScore + 150

            IF chessboard$(I, J) = "bpawn" THEN
                positionScore = positionScore - 10
                'At the end, passed pawns are a good thing...
                IF (Move > 30) AND (J < 5) THEN
                    positionScore = positionScore - 1
                END IF
                IF (Move > 30) AND (J < 4) THEN
                    positionScore = positionScore - 10
                END IF
                IF (Move > 30) AND (J < 2) THEN
                    positionScore = positionScore - 90
                END IF
            END IF

            IF chessboard$(I, J) = "brook" THEN positionScore = positionScore - 50

            IF chessboard$(I, J) = "bknight" THEN
                positionScore = positionScore - 30
                'At the end of the game, go close to the kings...
                IF Move > 30 AND (ABS(I - wkingPositionI) < 5 OR ABS(J - wkingPositionJ) < 5) THEN
                    positionScore = positionScore - 5
                END IF
            END IF

            IF chessboard$(I, J) = "bbishop" THEN positionScore = positionScore - 30

            IF chessboard$(I, J) = "bqueen" THEN positionScore = positionScore - 90

            IF chessboard$(I, J) = "bking" THEN positionScore = positionScore - 150

        NEXT J
    NEXT I

    'Check position quality
    'Take the center
    IF chessboard$(4, 3) = "wpawn" THEN positionScore = positionScore + 1
    IF chessboard$(4, 4) = "wpawn" THEN positionScore = positionScore + 1
    IF chessboard$(5, 3) = "wpawn" THEN positionScore = positionScore + 1
    IF chessboard$(5, 4) = "wpawn" THEN positionScore = positionScore + 1
    IF chessboard$(4, 5) = "bpawn" THEN positionScore = positionScore - 1
    IF chessboard$(4, 6) = "bpawn" THEN positionScore = positionScore - 1
    IF chessboard$(5, 5) = "bpawn" THEN positionScore = positionScore - 1
    IF chessboard$(5, 6) = "bpawn" THEN positionScore = positionScore - 1

    'In the opening, avoid stupid moves
    'White
    IF MoveNumber < 10 THEN
        'Do not move the rook
        IF chessboard$(1, 1) = "" THEN positionScore = positionScore - 1
        IF chessboard$(8, 1) = "" THEN positionScore = positionScore - 1
        'Do not move the knights at the edges
        IF chessboard$(1, 3) = "wknight" THEN positionScore = positionScore - 1
        IF chessboard$(8, 3) = "wknight" THEN positionScore = positionScore - 1
        'Do not move the queen
        IF chessboard$(4, 1) = "" THEN positionScore = positionScore - 1
        'Do not move the king
        IF chessboard$(5, 1) = "" THEN positionScore = positionScore - 1
        'Don't do stupid moves with pawns
        IF chessboard$(1, 4) = "wpawn" THEN positionScore = positionScore - 1
        IF chessboard$(8, 4) = "wpawn" THEN positionScore = positionScore - 1
    END IF
    'Black
    IF MoveNumber < 10 THEN
        'Do not move the rook
        IF chessboard$(1, 8) = "" THEN positionScore = positionScore + 1
        IF chessboard$(8, 8) = "" THEN positionScore = positionScore + 1
        'Do not move the knights at the edges
        IF chessboard$(1, 6) = "bknight" THEN positionScore = positionScore + 1
        IF chessboard$(8, 6) = "bknight" THEN positionScore = positionScore + 1
        'Do not move the queen
        IF chessboard$(4, 8) = "" THEN positionScore = positionScore + 1
        'Do not move the king
        IF chessboard$(5, 8) = "" THEN positionScore = positionScore + 1
        'Don't do stupid moves with pawns
        IF chessboard$(1, 5) = "bpawn" THEN positionScore = positionScore + 1
        IF chessboard$(8, 5) = "bpawn" THEN positionScore = positionScore + 1
    END IF

    IF (debugMode = 1) THEN PRINT "Position Score = " + STR$(positionScore)

END SUB


SUB HumanMove1 (HM1Skakiera() AS STRING)

    HumanMoveFound = 0

    'Scan the chessboard...
    FOR I = 1 TO 8
        FOR J = 1 TO 8

            'If you find a piece of the human...
            IF ((MID$(HM1Skakiera$(I, J), 1, 1) = "w" AND playerColor$ = "w") OR (MID$(HM1Skakiera$(I, J), 1, 1) = "b" AND playerColor$ = "b")) THEN

                IF debugMode = 1 THEN PRINT "Inside Human level 1 move - Checkpoint A"

                'Scan all possible destination squares...
                FOR ii = 1 TO 8
                    FOR jj = 1 TO 8

                        startingColumnHM1 = I
                        startingRankHM1 = J
                        finishingColumnHM1 = ii
                        finishingRankHM1 = jj

                        MovingPieceHM1$ = HM1Skakiera$(I, J)
                        ProsorinoKommatiHM1$ = HM1Skakiera$(ii, jj)

                        'Check legality of the move entered
                        whoPlays$ = "Human"
                        CALL ElegxosNomimotitas(HM1Skakiera$(), 0, startingColumnHM1, startingRankHM1, finishingColumnHM1, finishingRankHM1, MovingPieceHM1$)
                        whoPlays$ = "HY"

                        ' ------------------ Check the Check! START (14/3/2021) ------------------

                        'Temporarily do the move
                        HM1Skakiera$(finishingColumnHM1, finishingRankHM1) = HM1Skakiera$(startingColumnHM1, startingRankHM1)
                        HM1Skakiera$(startingColumnHM1, startingRankHM1) = ""

                        'Check the check
                        IF playerColor$ = "b" AND Nomimotita = 1 THEN
                            whoPlays$ = "HY"
                            CALL checkBlackCheck(HM1Skakiera$())
                            'Restore Nomimotita! (because it is 'broken' in the checkCheck function)
                            Nomimotita = 1
                            IF blackCheck = 1 THEN Nomimotita = 0
                            whoPlays$ = "Human"
                        END IF

                        IF playerColor$ = "w" AND Nomimotita = 1 THEN
                            whoPlays$ = "HY"
                            CALL checkWhiteCheck(HM1Skakiera$())
                            'Restore Nomimotita! (because it is 'broken' in the checkCheck function)
                            Nomimotita = 1
                            IF whiteCheck = 1 THEN Nomimotita = 0
                            whoPlays$ = "Human"
                        END IF

                        'Undo the move
                        HM1Skakiera$(startingColumnHM1, startingRankHM1) = MovingPieceHM1$
                        HM1Skakiera$(finishingColumnHM1, finishingRankHM1) = ProsorinoKommatiHM1$

                        ' ------------------ Check the Check! END (14/3/2021) ------------------

                        IF debugMode = 1 THEN
                            PRINT ""
                            PRINT "NEW MOVE ANALYZED: " + STR$(startingColumnHM1) + STR$(startingRankHM1) + " -> " + STR$(finishingColumnHM1) + STR$(finishingRankHM1)
                            PRINT "Legality of the move analyzed: " + STR$(Nomimotita)
                        END IF

                        'If move is legal, then do the move and present it in the chessbooard
                        IF Nomimotita = 1 THEN

                            HumanMoveFound = 1

                            'Do the move
                            HM1Skakiera$(finishingColumnHM1, finishingRankHM1) = HM1Skakiera$(startingColumnHM1, startingRankHM1)
                            HM1Skakiera$(startingColumnHM1, startingRankHM1) = ""

                            'Count the score of the move
                            CALL countScore

                            '-------------- MinMax --------------
                            'Store scores
                            NodesAnalysis1(NodeLevel_1_count, 1) = positionScore
                            ' Store parents
                            NodesAnalysis1(NodeLevel_1_count, 2) = NodeLevel_0_count

                            IF Move < thinkingDepth THEN
                                Move = Move + 1
                                CALL ComputerMove2(HM1Skakiera$())
                            END IF

                            'Undo the move
                            HM1Skakiera$(startingColumnHM1, startingRankHM1) = MovingPieceHM1$
                            HM1Skakiera$(finishingColumnHM1, finishingRankHM1) = ProsorinoKommatiHM1$

                            '-------------- MinMax --------------
                            'Increase node count
                            NodeLevel_1_count = NodeLevel_1_count + 1

                        END IF

                    NEXT jj
                NEXT ii

            END IF

        NEXT J
    NEXT I

    'Detect mate or stalemate (14/3/2021)
    IF (HumanMoveFound = 0) THEN
        'Detect mate if there is no human move found, but there is check! (14/3/2021)
        IF playerColor$ = "w" AND whiteCheck = 1 THEN
            MateFound = 1
            bestStartingRankMate = startingRank
            bestStartingColumnMate = startingColumn
            bestFinishingRankMate = finishingRank
            bestFinishingColumnMate = finishingColumn
        END IF
        IF playerColor$ = "b" AND blackCheck = 1 THEN
            MateFound = 1
            bestStartingRankMate = startingRank
            bestStartingColumnMate = startingColumn
            bestFinishingRankMate = finishingRank
            bestFinishingColumnMate = finishingColumn
        END IF
        'Detect stalemate (Pat in Greek) if there is no human move found, but there is check! (14/3/2021)
        IF playerColor$ = "w" AND whiteCheck = 0 THEN
            PatFound = 1
            bestStartingRankMate = startingRank
            bestStartingColumnMate = startingColumn
            bestFinishingRankMate = finishingRank
            bestFinishingColumnMate = finishingColumn
        END IF
        IF playerColor$ = "b" AND blackCheck = 0 THEN
            PatFound = 1
            bestStartingRankMate = startingRank
            bestStartingColumnMate = startingColumn
            bestFinishingRankMate = finishingRank
            bestFinishingColumnMate = finishingColumn
        END IF

    END IF

    IF playerColor$ = "b" THEN whichColorPlays$ = "White" '14/3/2021
    IF playerColor$ = "w" THEN whichColorPlays$ = "Black" '14/3/2021

    'Reduce the move
    Move = Move - 1

END SUB

SUB ComputerMove2 (CM2Skakiera() AS STRING)

    DIM bestMove2score AS INTEGER

    bestMove2score = 0

    'Scan the chessboard...
    FOR I = 1 TO 8
        FOR J = 1 TO 8

            'If you find a piece of the computer...
            IF ((MID$(CM2Skakiera$(I, J), 1, 1) = "w" AND playerColor$ = "b") OR (MID$(CM2Skakiera$(I, J), 1, 1) = "b" AND playerColor$ = "w")) THEN

                IF debugMode = 1 THEN PRINT "Inside Computer level 2 move - Checkpoint A"

                'Scan all possible destination squares...
                FOR ii = 1 TO 8
                    FOR jj = 1 TO 8

                        startingColumnCM2 = I
                        startingRankCM2 = J
                        finishingColumnCM2 = ii
                        finishingRankCM2 = jj

                        MovingPieceCM2$ = CM2Skakiera$(I, J)
                        ProsorinoKommatiCM2$ = CM2Skakiera$(ii, jj)

                        'Check legality of the move entered
                        CALL ElegxosNomimotitas(CM2Skakiera$(), 0, startingColumnCM2, startingRankCM2, finishingColumnCM2, finishingRankCM2, MovingPieceCM2$)

                        IF debugMode = 1 THEN
                            PRINT ""
                            PRINT "NEW MOVE ANALYZED: " + STR$(startingColumnCM2) + STR$(startingRankCM2) + " -> " + STR$(finishingColumnCM2) + STR$(finishingRankCM2)
                            PRINT "Legality of the move analyzed: " + STR$(Nomimotita)
                        END IF

                        'If move is legal, then do the move and present it in the chessbooard
                        IF Nomimotita = 1 THEN

                            'Do the move
                            CM2Skakiera$(finishingColumnCM2, finishingRankCM2) = CM2Skakiera$(startingColumnCM2, startingRankCM2)
                            CM2Skakiera$(startingColumnCM2, startingRankCM2) = ""

                            'Count the score of the move
                            CALL countScore

                            'PRINT "NodeLevel_2_count = " + STR$(NodeLevel_2_count)

                            '-------------- MinMax --------------
                            'Store scores
                            NodesAnalysis2(NodeLevel_2_count, 1) = positionScore
                            ' Store parents
                            NodesAnalysis2(NodeLevel_2_count, 2) = NodeLevel_1_count

                            'If the score is better than the existing best score, then this is the best move now (and the best score)
                            'IF ((playerColor$ = "b" AND positionScore >= bestPositionScore) OR (playerColor$ = "w" AND positionScore <= bestPositionScore)) THEN
                            '    bestStartingRank = startingRank
                            '    bestStartingColumn = startingColumn
                            '    bestFinishingRank = finishingRank
                            '    bestFinishingColumn = finishingColumn
                            '    bestPositionScore = positionScore
                            'END IF

                            'Call next level
                            'RULE: Only if the move entails the capturing of a piece! (14/3/2021)
                            IF Move < thinkingDepth AND ProsorinoKommatiCM2$ <> "" THEN
                                'IF Move < thinkingDepth THEN
                                'IF Move < thinkingDepth AND ((playerColor$ = "b" AND positionScore > bestMove2score) OR (playerColor$ = "w" AND positionScore < bestMove2score)) THEN
                                Move = Move + 1
                                bestMove2score = positionScore
                                CALL HumanMove3(CM2Skakiera$())
                            END IF

                            'Undo the move
                            CM2Skakiera$(startingColumnCM2, startingRankCM2) = MovingPieceCM2$
                            CM2Skakiera$(finishingColumnCM2, finishingRankCM2) = ProsorinoKommatiCM2$

                            '-------------- MinMax --------------
                            'Increase node count
                            NodeLevel_2_count = NodeLevel_2_count + 1

                        END IF

                    NEXT jj
                NEXT ii

            END IF

        NEXT J
    NEXT I

    'Reduce the move
    Move = Move - 1

END SUB


'-------------- MinMax --------------
SUB MinMax ()

    ' -------------------------------------------------------------------------------
    ' DO THE BEST MOVE FOUND
    ' Analyze only if possibility to eat back is not true!!!
    ' MessageBox.Show("Entered Best Move found area!")
    ' v0.990: Added the possibility_to_eat
    ' v0.991: Removed possibility to eat! Why not think everything?
    ' v0.991: Added the opening book check
    ' if ((possibility_to_eat_back = false) AND (possibility_to_eat = false))
    ' -------------------------------------------------------------------------------

    ' [MiniMax algorithm - skakos]
    ' MessageBox.Show("Entered checkpoint 1")
    ' Find node 1 move with the best score via the MiniMax algorithm.
    ' v0.980: Remove unsued counters.
    ' v0.990: Move 4 changes
    ' v0.991: Added counter4 again (needed if Thinking_Depth = 4)

    counter0 = 1
    counter1 = 1
    counter2 = 1
    counter3 = 1
    counter4 = 1

    ' -------------------------------------------------------------------
    ' NodesAnalysis
    ' -------------------------------------------------------------------
    ' Nodes structure...
    ' [ccc, xxx, 1]: Score of node No. ccc at level xxx
    ' [ccc, xxx, 2]: Parent of node No. ccc at level xxx-1
    ' -------------------------------------------------------------------

    ' ------- LOG: Nodes before (start) -------

    'Log not available in this edition - Check the graphics edition!

    ' ------- LOG: Nodes before (end) -------

    IF thinkingDepth = 5 THEN

        parentNodeAnalyzed = -999

        ' Move 4 level (Computer) -- The analysis starts from here if Thinking_Depth = 4.

        ' Note: Start from 1!

        'PRINT "NodeLevel_4_count = " + STR$(NodeLevel_4_count)
        'PRINT "NodesAnalysis4(counter4, 1) = " + STR$(NodesAnalysis4(counter4, 1))
        'PRINT "NodesAnalysis4(counter4, 2) = " + STR$(NodesAnalysis4(counter4, 2))
        'PRINT "NodesAnalysis3(NodesAnalysis4(counter4, 2), 1) = " + STR$(NodesAnalysis3(NodesAnalysis4(counter4, 2), 1))

        FOR counter4 = 1 TO (NodeLevel_4_count - 1)

            IF (NodesAnalysis4(counter4, 2) <> parentNodeAnalyzed) THEN
                parentNodeAnalyzed = NodesAnalysis4(counter4, 2)
                'PRINT "counter4 = " + STR$(counter4)
                IF NodesAnalysis4(counter4, 2) = 0 THEN NodesAnalysis4(counter4, 2) = 1
                NodesAnalysis3(NodesAnalysis4(counter4, 2), 1) = NodesAnalysis4(counter4, 1)
                bestNode4 = counter4
                bestNodes4(parentNodeAnalyzed) = counter4
            END IF

            ' v0.991: Original: >=
            ' v0.991: This should depend on the colour of the computer!!!
            ' v0.991: Tried to fix the problem in MinMax. Node1 elements for the SAME parent of Node2 must be filled accordingly.
            '         We do not need to take into account the Node2 elements which are empty, thus having a score of 0 but no
            '         assigned move! (this is why the Best Variant text is empty in the first moves)
            IF playerColor$ = "w" THEN
                IF (NodesAnalysis4(counter4, 1) <= NodesAnalysis3(NodesAnalysis4(counter4, 2), 1)) THEN
                    IF NodesAnalysis4(counter4, 2) = 0 THEN NodesAnalysis4(counter4, 2) = 1
                    NodesAnalysis3(NodesAnalysis4(counter4, 2), 1) = NodesAnalysis4(counter4, 1)
                    bestNode4 = counter4
                    bestNodes4(parentNodeAnalyzed) = counter4
                END IF
            ELSEIF (playerColor$ = "b") THEN
                IF (NodesAnalysis4(counter4, 1) >= NodesAnalysis3(NodesAnalysis4(counter4, 2), 1)) THEN
                    IF NodesAnalysis4(counter4, 2) = 0 THEN NodesAnalysis4(counter4, 2) = 1
                    NodesAnalysis3(NodesAnalysis4(counter4, 2), 1) = NodesAnalysis4(counter4, 1)
                    bestNode4 = counter4
                    bestNodes4(parentNodeAnalyzed) = counter4
                END IF
            END IF

        NEXT counter4

        ' Now the Node1 level is filled with the score data
        ' this is line 1 in the shape at http:'upload.wikimedia.org/wikipedia/commons/thumb/6/6f/Minimax.svg/300px-Minimax.svg.png

        ' Move 3 level (Human)

        parentNodeAnalyzed = -999

        ' Note: Start from 1!
        FOR counter3 = 1 TO (NodeLevel_3_count - 1)

            IF (NodesAnalysis3(counter3, 2) <> parentNodeAnalyzed) THEN
                parentNodeAnalyzed = NodesAnalysis3(counter3, 2)
                IF NodesAnalysis3(counter3, 2) = 0 THEN NodesAnalysis3(counter3, 2) = 1
                NodesAnalysis2(NodesAnalysis3(counter3, 2), 1) = NodesAnalysis3(counter3, 1)
                bestNode3 = counter3
                bestNodes3(parentNodeAnalyzed) = counter3
            END IF

            ' v0.991: Choose different based on colour!
            IF (playerColor$ = "w") THEN
                IF NodesAnalysis3(counter3, 1) >= NodesAnalysis2(NodesAnalysis3(counter3, 2), 1) THEN
                    IF NodesAnalysis3(counter3, 2) = 0 THEN NodesAnalysis3(counter3, 2) = 1
                    NodesAnalysis2(NodesAnalysis3(counter3, 2), 1) = NodesAnalysis3(counter3, 1)
                    bestNode3 = counter3
                    bestNodes3(parentNodeAnalyzed) = counter3
                END IF
            ELSEIF (playerColor$ = "b") THEN
                IF NodesAnalysis3(counter3, 1) <= NodesAnalysis2(NodesAnalysis3(counter3, 2), 1) THEN
                    IF NodesAnalysis3(counter3, 2) = 0 THEN NodesAnalysis3(counter3, 2) = 1
                    NodesAnalysis2(NodesAnalysis3(counter3, 2), 1) = NodesAnalysis3(counter3, 1)
                    bestNode3 = counter3
                    bestNodes3(parentNodeAnalyzed) = counter3
                END IF
            END IF

        NEXT counter3

    END IF

    parentNodeAnalyzed = -999

    ' Move 2 level (Computer) -- The analysis starts from here if Thinking_Depth = 2.

    ' Note: Start from 1!

    FOR counter2 = 1 TO (NodeLevel_2_count - 1)

        IF debugMode = 1 THEN
            PRINT "counter2 = " + STR$(counter2)
            PRINT "NodesAnalysis2(counter2, 2) = " + STR$(NodesAnalysis2(counter2, 2))
            PRINT "NodesAnalysis1(NodesAnalysis2(counter2, 2), 1) = " + STR$(NodesAnalysis1(NodesAnalysis2(counter2, 2), 1))
        END IF

        IF (NodesAnalysis2(counter2, 2) <> parentNodeAnalyzed) THEN
            parentNodeAnalyzed = NodesAnalysis2(counter2, 2)
            NodesAnalysis1(NodesAnalysis2(counter2, 2), 1) = NodesAnalysis2(counter2, 1)
            bestNode2 = counter2
            IF debugMode = 1 THEN
                PRINT "parentNodeAnalyzed = " + STR$(parentNodeAnalyzed)
                PRINT "parentNodeAnalyzed = " + STR$(parentNodeAnalyzed)
            END IF
            bestNodes2(parentNodeAnalyzed) = counter2
        END IF

        ' v0.991: Original: >=
        ' v0.991: This should depend on the colour of the computer!!!
        ' v0.991: Tried to fix the problem in MinMax. Node1 elements for the SAME parent of Node2 must be filled accordingly.
        '         We do not need to take into account the Node2 elements which are empty, thus having a score of 0 but no
        '         assigned move! (this is why the Best Variant text is empty in the first moves)
        IF playerColor$ = "w" THEN
            IF (NodesAnalysis2(counter2, 1) <= NodesAnalysis1(NodesAnalysis2(counter2, 2), 1)) THEN
                NodesAnalysis1(NodesAnalysis2(counter2, 2), 1) = NodesAnalysis2(counter2, 1)
                bestNode2 = counter2
                bestNodes2(parentNodeAnalyzed) = counter2
            END IF
        ELSEIF (playerColor$ = "b") THEN
            IF (NodesAnalysis2(counter2, 1) >= NodesAnalysis1(NodesAnalysis2(counter2, 2), 1)) THEN
                NodesAnalysis1(NodesAnalysis2(counter2, 2), 1) = NodesAnalysis2(counter2, 1)
                bestNode2 = counter2
                bestNodes2(parentNodeAnalyzed) = counter2
            END IF
        END IF

    NEXT counter2

    ' Now the Node1 level is filled with the score data
    ' this is line 1 in the shape at http:'upload.wikimedia.org/wikipedia/commons/thumb/6/6f/Minimax.svg/300px-Minimax.svg.png

    ' Move 1 level (Human)

    parentNodeAnalyzed = -999

    ' Note: Start from 1!
    FOR counter1 = 1 TO (NodeLevel_1_count - 1)

        IF (NodesAnalysis1(counter1, 2) <> parentNodeAnalyzed) THEN
            parentNodeAnalyzed = NodesAnalysis1(counter1, 2)
            NodesAnalysis0(NodesAnalysis1(counter1, 2), 1) = NodesAnalysis1(counter1, 1)
            bestNode1 = counter1
            bestNodes1(parentNodeAnalyzed) = counter1
        END IF

        ' v0.991: Choose different based on colour!
        IF (playerColor$ = "w") THEN
            IF NodesAnalysis1(counter1, 1) >= NodesAnalysis0(NodesAnalysis1(counter1, 2), 1) THEN
                NodesAnalysis0(NodesAnalysis1(counter1, 2), 1) = NodesAnalysis1(counter1, 1)
                bestNode1 = counter1
                bestNodes1(parentNodeAnalyzed) = counter1
            END IF
        ELSEIF (playerColor$ = "b") THEN
            IF NodesAnalysis1(counter1, 1) <= NodesAnalysis0(NodesAnalysis1(counter1, 2), 1) THEN
                NodesAnalysis0(NodesAnalysis1(counter1, 2), 1) = NodesAnalysis1(counter1, 1)
                bestNode1 = counter1
                bestNodes1(parentNodeAnalyzed) = counter1
            END IF
        END IF

    NEXT counter1

    ' Choose the biggest score at the Node0 level
    ' Check example at http:'en.wikipedia.org/wiki/Minimax#Example_2
    ' This is line 0 at the shape at http:'upload.wikimedia.org/wikipedia/commons/thumb/6/6f/Minimax.svg/300px-Minimax.svg.png

    ' Move 0 level (Computer)

    ' Initialize the score with the first score and move found
    ' Note: Start from 1!
    temp_score = NodesAnalysis0(1, 1)
    ' v0.992: Start from 0 also here!
    bestStartingColumn = NodesAnalysis0(1, 3)
    bestStartingRank = NodesAnalysis0(1, 5)
    bestFinishingColumn = NodesAnalysis0(1, 4)
    bestFinishingRank = NodesAnalysis0(1, 6)
    ' v0.992
    bestNode0 = 0

    'PRINT "Best move  : " + STR$(bestStartingColumn) + STR$(bestStartingRank) + " -> " + STR$(bestFinishingColumn) + STR$(bestFinishingRank)
    'PRINT "Best score : " + STR$(temp_score)
    'INPUT A$

    'Note: Start from 1!
    FOR counter0 = 1 TO (NodeLevel_0_count - 1)

        ' v0.991: Choose different based on colour!
        IF (playerColor$ = "b") THEN
            IF (NodesAnalysis0(counter0, 1) > temp_score) THEN
                temp_score = NodesAnalysis0(counter0, 1)
                bestStartingColumn = NodesAnalysis0(counter0, 3)
                bestStartingRank = NodesAnalysis0(counter0, 5)
                bestFinishingColumn = NodesAnalysis0(counter0, 4)
                bestFinishingRank = NodesAnalysis0(counter0, 6)
                ' v0.992
                bestNode0 = counter0
            END IF
        ELSEIF (playerColor$ = "w") THEN
            IF NodesAnalysis0(counter0, 1) < temp_score THEN
                temp_score = NodesAnalysis0(counter0, 1)
                bestStartingColumn = NodesAnalysis0(counter0, 3)
                bestStartingRank = NodesAnalysis0(counter0, 5)
                bestFinishingColumn = NodesAnalysis0(counter0, 4)
                bestFinishingRank = NodesAnalysis0(counter0, 6)
                ' v0.992
                bestNode0 = counter0
            END IF
        END IF

    NEXT counter0

    ' ------- LOG: Nodes after (start) -------

    'Log not available in this edition - Check the graphics edition!

    ' ------- LOG: Nodes after (end) -------

END SUB

SUB HumanMove3 (HM3Skakiera() AS STRING)

    DIM bestMove3score AS INTEGER

    bestMove3score = 0

    'Scan the chessboard...
    FOR I = 1 TO 8
        FOR J = 1 TO 8

            'If you find a piece of the human...
            IF ((MID$(HM3Skakiera$(I, J), 1, 1) = "w" AND playerColor$ = "w") OR (MID$(HM3Skakiera$(I, J), 1, 1) = "b" AND playerColor$ = "b")) THEN

                IF debugMode = 1 THEN PRINT "Inside Human level 3 move - Checkpoint A"

                'Scan all possible destination squares...
                FOR ii = 1 TO 8
                    FOR jj = 1 TO 8

                        startingColumnHM3 = I
                        startingRankHM3 = J
                        finishingColumnHM3 = ii
                        finishingRankHM3 = jj

                        MovingPieceHM3$ = HM3Skakiera$(I, J)
                        ProsorinoKommatiHM3$ = HM3Skakiera$(ii, jj)

                        'Check legality of the move entered
                        whoPlays$ = "Human"
                        CALL ElegxosNomimotitas(HM3Skakiera$(), 0, startingColumnHM3, startingRankHM3, finishingColumnHM3, finishingRankHM3, MovingPieceHM3$)
                        whoPlays$ = "HY"

                        IF debugMode = 1 THEN
                            PRINT ""
                            PRINT "NEW MOVE ANALYZED: " + STR$(startingColumnHM3) + STR$(startingRankHM3) + " -> " + STR$(finishingColumnHM3) + STR$(finishingRankHM3)
                            PRINT "Legality of the move analyzed: " + STR$(Nomimotita)
                        END IF

                        'If move is legal, then do the move and present it in the chessbooard
                        IF Nomimotita = 1 THEN

                            'Do the move
                            HM3Skakiera$(finishingColumnHM3, finishingRankHM3) = HM3Skakiera$(startingColumnHM3, startingRankHM3)
                            HM3Skakiera$(startingColumnHM3, startingRankHM3) = ""

                            'Count the score of the move
                            CALL countScore

                            'PRINT "NodeLevel_3_count = " + STR$(NodeLevel_3_count)

                            '-------------- MinMax --------------
                            'Store scores
                            NodesAnalysis3(NodeLevel_3_count, 1) = positionScore
                            ' Store parents
                            NodesAnalysis3(NodeLevel_3_count, 2) = NodeLevel_2_count

                            'Call the next level only if the variant entails capturing a piece (14/3/2021)
                            IF Move < thinkingDepth AND ProsorinoKommatiHM3$ <> "" THEN
                                'IF Move < thinkingDepth AND ((playerColor$ = "b" AND positionScore <= bestMove3score) OR (playerColor$ = "w" AND positionScore >= bestMove3score)) THEN
                                Move = Move + 1
                                bestMove3score = positionScore
                                CALL ComputerMove4(HM3Skakiera$())
                            END IF

                            'Undo the move
                            HM3Skakiera$(startingColumnHM3, startingRankHM3) = MovingPieceHM3$
                            HM3Skakiera$(finishingColumnHM3, finishingRankHM3) = ProsorinoKommatiHM3$

                            '-------------- MinMax --------------
                            'Increase node count
                            NodeLevel_3_count = NodeLevel_3_count + 1

                        END IF

                    NEXT jj
                NEXT ii

            END IF

        NEXT J
    NEXT I

    'Reduce the move
    Move = Move - 1

END SUB

SUB ComputerMove4 (CM4Skakiera() AS STRING)

    'Scan the chessboard...
    FOR I = 1 TO 8
        FOR J = 1 TO 8

            'If you find a piece of the computer...
            IF ((MID$(CM4Skakiera$(I, J), 1, 1) = "w" AND playerColor$ = "b") OR (MID$(CM4Skakiera$(I, J), 1, 1) = "b" AND playerColor$ = "w")) THEN

                IF debugMode = 1 THEN PRINT "Inside Computer level 4 move - Checkpoint A"

                'Scan all possible destination squares...
                FOR ii = 1 TO 8
                    FOR jj = 1 TO 8

                        startingColumnCM4 = I
                        startingRankCM4 = J
                        finishingColumnCM4 = ii
                        finishingRankCM4 = jj

                        MovingPieceCM4$ = CM4Skakiera$(I, J)
                        ProsorinoKommatiCM4$ = CM4Skakiera$(ii, jj)

                        'Check legality of the move entered
                        CALL ElegxosNomimotitas(CM4Skakiera$(), 0, startingColumnCM4, startingRankCM4, finishingColumnCM4, finishingRankCM4, MovingPieceCM4$)

                        IF debugMode = 1 THEN
                            PRINT ""
                            PRINT "NEW MOVE ANALYZED: " + STR$(startingColumnCM4) + STR$(startingRankCM4) + " -> " + STR$(finishingColumnCM4) + STR$(finishingRankCM4)
                            PRINT "Legality of the move analyzed: " + STR$(Nomimotita)
                        END IF

                        'If move is legal, then do the move and present it in the chessbooard
                        IF Nomimotita = 1 THEN

                            'Do the move
                            CM4Skakiera$(finishingColumnCM4, finishingRankCM4) = CM4Skakiera$(startingColumnCM4, startingRankCM4)
                            CM4Skakiera$(startingColumnCM4, startingRankCM4) = ""

                            'Count the score of the move
                            CALL countScore

                            '-------------- MinMax --------------
                            'Store scores
                            NodesAnalysis4(NodeLevel_4_count, 1) = positionScore
                            ' Store parents
                            NodesAnalysis4(NodeLevel_4_count, 2) = NodeLevel_3_count

                            'If the score is better than the existing best score, then this is the best move now (and the best score)
                            'This is not needed. Why store that move? Minimax defines the best move anyway.
                            'IF ((playerColor$ = "b" AND positionScore >= bestPositionScore) OR (playerColor$ = "w" AND positionScore <= bestPositionScore)) THEN
                            '    bestStartingRank = startingRank
                            '    bestStartingColumn = startingColumn
                            '    bestFinishingRank = finishingRank
                            '    bestFinishingColumn = finishingColumn
                            '    bestPositionScore = positionScore
                            'END IF

                            'Undo the move
                            CM4Skakiera$(startingColumnCM4, startingRankCM4) = MovingPieceCM4$
                            CM4Skakiera$(finishingColumnCM4, finishingRankCM4) = ProsorinoKommatiCM4$

                            '-------------- MinMax --------------
                            'Increase node count
                            NodeLevel_4_count = NodeLevel_4_count + 1

                        END IF

                    NEXT jj
                NEXT ii

            END IF

        NEXT J
    NEXT I

    'Reduce the move
    Move = Move - 1

END SUB


SUB PawnPromotion ()

    FOR KK = 1 TO 8
        IF chessboard$(KK, 1) = "bpawn" THEN chessboard$(KK, 1) = "bqueen"
    NEXT KK

    FOR YY = 1 TO 8
        IF chessboard$(YY, 8) = "wpawn" THEN chessboard$(YY, 8) = "wqueen"
    NEXT YY

END SUB


SUB Castling ()

    'White castling
    IF startingRank = 1 AND finishingRank = 1 AND startingColumn = 5 AND finishingColumn = 3 AND MovingPiece$ = "wking" AND playerColor$ = "w" THEN
        IF chessboard$(4, 1) = "" AND chessboard$(3, 1) = "" AND chessboard$(2, 1) = "" AND chessboard$(1, 1) = "wrook" AND whiteCastling = 0 THEN
            Nomimotita = 1
            whiteCastling = 1
            whiteBigCastling = 1
        END IF
    ELSEIF startingRank = 1 AND finishingRank = 1 AND startingColumn = 5 AND finishingColumn = 7 AND MovingPiece$ = "wking" AND playerColor$ = "w" THEN
        IF chessboard$(6, 1) = "" AND chessboard$(7, 1) = "" AND chessboard$(8, 1) = "wrook" AND whiteCastling = 0 THEN
            Nomimotita = 1
            whiteCastling = 1
            whiteSmallCastling = 1
        END IF
    END IF

    'Black castling
    IF startingRank = 8 AND finishingRank = 8 AND startingColumn = 5 AND finishingColumn = 3 AND MovingPiece$ = "bking" AND playerColor$ = "b" THEN
        IF chessboard$(4, 8) = "" AND chessboard$(3, 8) = "" AND chessboard$(2, 8) = "" AND chessboard$(1, 8) = "brook" AND blackCastling = 0 THEN
            Nomimotita = 1
            blackCastling = 1
            blackBigCastling = 1
        END IF
    ELSEIF startingRank = 8 AND finishingRank = 8 AND startingColumn = 5 AND finishingColumn = 7 AND MovingPiece$ = "bking" AND playerColor$ = "b" THEN
        IF chessboard$(6, 8) = "" AND chessboard$(7, 8) = "" AND chessboard$(8, 8) = "brook" AND blackCastling = 0 THEN
            Nomimotita = 1
            blackCastling = 1
            blackSmallCastling = 1
        END IF
    END IF

END SUB


SUB checkWhiteCheck (CWCSkakiera() AS STRING)

    whiteCheck = 0

    'PRINT "Check check START: Nomimotita = " + STR$(Nomimotita)

    'Scan the chessboard...
    FOR I1 = 1 TO 8
        FOR J1 = 1 TO 8

            'If you find a black piece...
            IF MID$(CWCSkakiera$(I1, J1), 1, 1) = "b" THEN

                'Scan all possible destination squares...
                FOR ii1 = 1 TO 8
                    FOR jj1 = 1 TO 8

                        startingColumnCWC = I1
                        startingRankCWC = J1
                        finishingColumnCWC = ii1
                        finishingRankCWC = jj1

                        MovingPieceCWC$ = CWCSkakiera$(I1, J1)
                        ProsorinoKommatiCWC$ = CWCSkakiera$(ii1, jj1)

                        'Check legality of the move entered if the target is the White King!
                        IF ProsorinoKommatiCWC$ = "wking" THEN

                            CalledFromCheckCheck = 1 '14/3/2021
                            CALL ElegxosNomimotitas(CWCSkakiera$(), 0, startingColumnCWC, startingRankCWC, finishingColumnCWC, finishingRankCWC, MovingPieceCWC$)

                            'If move is legal, then do the move and present it in the chessbooard
                            IF Nomimotita = 1 THEN whiteCheck = 1

                            'IF Nomimotita = 1 THEN PRINT "Found legal check move: " + STR$(startingColumnCWC) + STR$(startingRankCWC) + " -> " + STR$(finishingColumnCWC) + STR$(finishingRankCWC): INPUT h$

                        END IF

                    NEXT jj1
                NEXT ii1

            END IF

        NEXT J1
    NEXT I1

END SUB


SUB checkBlackCheck (CBCSkakiera() AS STRING)

    blackCheck = 0

    'Scan the chessboard...
    FOR I2 = 1 TO 8
        FOR J2 = 1 TO 8

            'If you find a black piece...
            IF MID$(CBCSkakiera$(I2, J2), 1, 1) = "w" THEN

                'Scan all possible destination squares...
                FOR ii2 = 1 TO 8
                    FOR jj2 = 1 TO 8

                        startingColumnCBC = I2
                        startingRankCBC = J2
                        finishingColumnCBC = ii2
                        finishingRankCBC = jj2

                        MovingPieceCBC$ = CBCSkakiera$(I2, J2)
                        ProsorinoKommatiCBC$ = CBCSkakiera$(ii2, jj2)

                        'Check legality of the move entered if the target is the Black King!
                        IF ProsorinoKommatiCBC$ = "bking" THEN

                            'IF startingColumnCBC = 3 AND startingRankCBC = 7 AND finishingColumnCBC = 5 AND finishingRankCBC = 8 THEN
                            '    PRINT "MovingPieceCBC$ = " + MovingPieceCBC$
                            '    PRINT "ProsorinoKommatiCBC$ = " + ProsorinoKommatiCBC$
                            '    INPUT aa$
                            'END IF

                            CalledFromCheckCheck = 1 '14/3/2021
                            CALL ElegxosNomimotitas(CBCSkakiera$(), 0, startingColumnCBC, startingRankCBC, finishingColumnCBC, finishingRankCBC, MovingPieceCBC$)

                            'If move is legal, then do the move and present it in the chessbooard
                            IF Nomimotita = 1 THEN blackCheck = 1

                            'IF startingColumnCBC = 3 AND startingRankCBC = 7 AND finishingColumnCBC = 5 AND finishingRankCBC = 8 THEN
                            '    PRINT "Nomimotita = " + STR$(Nomimotita)
                            '    PRINT "blackCheck = " + STR$(blackCheck)
                            '    INPUT aa$
                            'END IF

                        END IF

                    NEXT jj2
                NEXT ii2

            END IF

        NEXT J2
    NEXT I2

END SUB


