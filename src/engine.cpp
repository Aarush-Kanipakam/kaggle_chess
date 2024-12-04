#include <algorithm>
#include <random>
#include <iostream>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include "board.hpp" 
#include "engine.hpp"
#include "butils.hpp"

#define INT_MAX 1000000007

struct evalweights {
    float king;
    float bishop;
    float rook;
    float pawn;
    float total_moves;
    float king_moves;
    float king_safety;
    float development;
};

evalweights weights = {10000.0, 6.0, 7.0, 3.0, 0.0, 0.0, 0.0, 0.0}; //weights for the evaluation function

struct eval {
    /* Heuristic parameters we are considering 
        King,
        Bishop
        Rook,
        Pawn,
        Total num. of valid moves 
        Total num. of valid moves for the king 
        King Safety - How many neighbouring squares of the king are guarded 
        Development - How many peices are there in their non original position 
        Dominancy - If peices of one color dominate a quadrant while others are spread over throughout 
        Pawn Promotion - How many pawns are close to promotion
        Board control - How many squares are controlled by each player
        Corner control - How many corners are controlled by each player
        Piece Synergy - How many pieces are working together
        */
    int king[2]; //handled this
    int bishop[2]; //handled this
    int rook[2]; //handled this
    int pawn[2]; //handled this
    float bishop_pos[2];
    float rook_pos[2];
    float pawn_pos[2];
    float check[2];
};

int newcount = 0; //keeps track of how many new positions have been evaluated so far
int fetchcount = 0; //keeps track of how many positions were retrieved from transposition table
int quiscount = 0; //keeps track of how many positions were evaluated in quiescence search
// std::atomic<bool> *searchstatus; //keeps track of whether the search is still going on or not
int drawdetections = 0;
std::random_device rd;
std::mt19937_64 generator(rd()); //random 64 bit generator for zobrish hashing

//HashEntry stores the transposition table object containing information about the position stored
class HashEntry{
    public:
        unsigned long long int zobrish;
        int depth;
        int type; //0 = exact, 1 = lowerbound, 2 = upperbound
        float eval;
        U16 move; //best move for the position, if exists

        // Constructor without parameter for "new" keyword
        HashEntry() { 
            this->zobrish = 0;
        }

        // Constructor with parameters for actually creating a hash entry
        HashEntry(unsigned long long int zobrish, int depth, int type, float eval, U16 move){
            this->zobrish = zobrish;
            this->depth = depth;
            this->type = type;
            this->eval = eval;
            this->move = move;
        }
};

//Transposition table stores information about board states which have already been encountered before
class TranspositionTable{
    public:
        HashEntry* hashTable; //array of hash entries - the deepest entries
        HashEntry* activeHashTable; //array of hash entries - latest entries 
        int size; //size of the transposition table
        unsigned long long int pieceHashCodes[64][10]; //zobrish hash codes for each piece on each square; 4 peices * 2 colours
        unsigned long long int sideHashCodes[2]; //zobrish hash codes for the side to play

        //Constructor for the transposition table; creates the Transposition table and initializes the zobrish hash codes
        TranspositionTable(int size){
            this->size = size;
            this->hashTable = new HashEntry[size];
            this->activeHashTable = new HashEntry[size];
            // std::cout << "Initializing Zobrish table" << std::endl;
            sideHashCodes[0] = generator(); //white to play
            sideHashCodes[1] = generator(); //black to play
            for (int i = 0; i < 64; i ++){
                for (int j = 0; j < 10; j ++){ //4 pieces and 2 colors and 2 for side to play
                    pieceHashCodes[i][j] = generator();
                    // std::cout << "i: " << i << " j: " << j << " zobrish: " << pieceHashCodes[i][j] << std::endl;
                }
            }
            // std::cout << "Zobrish table initialized" << std::endl;
        }

        //Finds the hash of the board
        unsigned long long int findhash(const Board& b){ //finds the hash of the board
            unsigned long long int hash = 0;
            if (b.data.player_to_play == WHITE){
                hash ^= sideHashCodes[0];
            }
            else{
                hash ^= sideHashCodes[1];
            }
            U8 w_king1 = b.data.w_king;U8 b_king1 = b.data.b_king;U8 w_rook_ws1 = b.data.w_rook_1;U8 w_rook_bs1 = b.data.w_rook_2;U8 b_rook_ws1 = b.data.b_rook_1;U8 b_rook_bs1 = b.data.b_rook_2;U8 w_bishop1 = b.data.w_bishop;U8 b_bishop1 = b.data.b_bishop;U8 w_pawn_ws1 = b.data.w_pawn_1;U8 w_pawn_bs1 = b.data.w_pawn_2;U8 b_pawn_ws1 = b.data.b_pawn_1;U8 b_pawn_bs1 = b.data.b_pawn_2; U8 w_knight_1 = b.data.w_knight_1; U8 w_knight_2 = b.data.w_knight_2; U8 b_knight_1 = b.data.b_knight_1; U8 b_knight_2 = b.data.b_knight_2;

            if (w_king1 != DEAD){
                hash ^= pieceHashCodes[w_king1][0];
            }
            if (b_king1 != DEAD){
                hash ^= pieceHashCodes[b_king1][1];
            }
            if (w_rook_ws1 != DEAD){
                hash ^= pieceHashCodes[w_rook_ws1][4];
            }
            if (w_rook_bs1 != DEAD){
                hash ^= pieceHashCodes[w_rook_bs1][4];
            }
            if (b_rook_ws1 != DEAD){
                hash ^= pieceHashCodes[b_rook_ws1][5];
            }
            if (b_rook_bs1 != DEAD){
                hash ^= pieceHashCodes[b_rook_bs1][5];
            }
            if (w_bishop1 != DEAD){
                hash ^= pieceHashCodes[w_bishop1][2];
            }
            if (b_bishop1 != DEAD){
                hash ^= pieceHashCodes[b_bishop1][3];
            }
            if (w_pawn_ws1 != DEAD){
                if(b.data.board_0[w_pawn_ws1] & PAWN){hash ^= pieceHashCodes[w_pawn_ws1][6];}else if(b.data.board_0[w_pawn_ws1] & BISHOP){hash ^= pieceHashCodes[w_pawn_ws1][2];}else if(b.data.board_0[w_pawn_ws1] & ROOK){hash ^= pieceHashCodes[w_pawn_ws1][4];}
            }
            if (w_pawn_bs1 != DEAD){
                if(b.data.board_0[w_pawn_bs1] & PAWN){hash ^= pieceHashCodes[w_pawn_bs1][6];}else if(b.data.board_0[w_pawn_bs1] & BISHOP){hash ^= pieceHashCodes[w_pawn_bs1][2];}else if(b.data.board_0[w_pawn_bs1] & ROOK){hash ^= pieceHashCodes[w_pawn_bs1][4];}
            }
            if (b_pawn_ws1 != DEAD){
                if(b.data.board_0[b_pawn_ws1] & PAWN){hash ^= pieceHashCodes[b_pawn_ws1][7];}else if(b.data.board_0[b_pawn_ws1] & BISHOP){hash ^= pieceHashCodes[b_pawn_ws1][3];}else if(b.data.board_0[b_pawn_ws1] & ROOK){hash ^= pieceHashCodes[b_pawn_ws1][5];}
            }
            if (b_pawn_bs1 != DEAD){
                if(b.data.board_0[b_pawn_bs1] & PAWN){hash ^= pieceHashCodes[b_pawn_bs1][7];}else if(b.data.board_0[b_pawn_bs1] & BISHOP){hash ^= pieceHashCodes[b_pawn_bs1][3];}else if(b.data.board_0[b_pawn_bs1] & ROOK){hash ^= pieceHashCodes[b_pawn_bs1][5];}
            }
            if (w_knight_1 != DEAD){
                hash ^= pieceHashCodes[w_knight_1][8];
            }
            if (w_knight_2 != DEAD){
                hash ^= pieceHashCodes[w_knight_2][8];
            }
            if (b_knight_1 != DEAD){
                hash ^= pieceHashCodes[b_knight_1][9];
            }
            if (b_knight_2 != DEAD){
                hash ^= pieceHashCodes[b_knight_2][9];
            }
            return hash;
        }

        //Inserts a new board positon into the transposition table
        void insert(const Board &b, int depth, int type, float eval, U16 move = 0){
            unsigned long long int zobrish = findhash(b);
            HashEntry entry(zobrish, depth, type, eval, move);
            int index = entry.zobrish % size;
            activeHashTable[index] = entry;
            if (hashTable[index].zobrish == 0){
                hashTable[index] = entry;
            }else{
                if (hashTable[index].depth < depth){ //replaces if depth is higher, doesnt really matter if position is different though in this case, could add bucketing
                    hashTable[index] = entry;
                }
            }
            
        }
        
        //Checks if a board position already exists in the transposition table
        bool exists(const Board &b){
            unsigned long long int zobrish = findhash(b);
            int index = zobrish % size;
            std::cout << "index: " << index << " zobrish: " << zobrish << std::endl;
            if (hashTable[index].zobrish == zobrish || activeHashTable[index].zobrish == zobrish){
                return true;
            }
            return false;
        }

        //Returns the information of a board position
        HashEntry* getEntry(const Board &b){
            unsigned long long int zobrish = findhash(b);
            int index = zobrish % size;
            if (hashTable[index].zobrish == zobrish){
                return &hashTable[index];
            }
            return &activeHashTable[index];
        }
};

//define variables
TranspositionTable transpositionTable(10000000); //10^7
// std::vector <unsigned long long int> historyStack; //keeps track of the history of the current line - for draw detection - not a stack just for namesake
U16 principalVariation; //stores the principal variation for the current line
int maxdepth = 0; //stores the max depth reached
float contemptFactor = -0.2; //contempt factor for draw detection
std::unordered_map<U8, float> hurestics_rook_black = {{pos(0,6), 1.0}, {pos(1,6), 0.0}, {pos(2,6), 1.0}, {pos(3,6), 1.0}, {pos(4,6), 1.0}, {pos(5,6), 2.0}, {pos(6,6), 2.0},{pos(0,5), 1.0}, {pos(1,5), 0.0}, {pos(2,5), 0.0}, {pos(3,5), 0.0}, {pos(4,5), 0.0}, {pos(5,5), 0.0}, {pos(6,5), 2.0},{pos(0,4), 1.0}, {pos(1,4), 0.0},                                                    {pos(5,4), 0.0}, {pos(6,4), 1.5},{pos(0,3), 1.0}, {pos(1,3), 0.0},                                                    {pos(5,3), 0.0}, {pos(6,3), 1.5},{pos(0,2), 1.0}, {pos(1,2), 0.0},                                                    {pos(5,2), 0.0}, {pos(6,2), 1.5},{pos(0,1), 1.0}, {pos(1,1), 0.0}, {pos(2,1), 0.0}, {pos(3,1), 0.0}, {pos(4,1), 0.0}, {pos(5,1), 0.0}, {pos(6,1), 3.0},{pos(0,0), 1.0}, {pos(1,0), 2.0}, {pos(2,0), 1.0}, {pos(3,0), 1.0}, {pos(4,0), 1.0}, {pos(5,0), 1.0}, {pos(6,0), 1.5},};std::unordered_map<U8, float> hurestics_rook_white = {{pos(0,6), 1.5}, {pos(1,6), 1.0}, {pos(2,6), 1.0}, {pos(3,6), 1.0}, {pos(4,6), 1.0}, {pos(5,6), 2.0}, {pos(6,6), 1.0}, {pos(0,5), 3.0}, {pos(1,5), 0.0}, {pos(2,5), 0.0}, {pos(3,5), 0.0}, {pos(4,5), 0.0}, {pos(5,5), 0.0}, {pos(6,5), 1.0},{pos(0,4), 1.5}, {pos(1,4), 0.0},                                                    {pos(5,4), 0.0}, {pos(6,4), 1.0},{pos(0,3), 1.5}, {pos(1,3), 0.0},                                                    {pos(5,3), 0.0}, {pos(6,3), 1.0},{pos(0,2), 1.5}, {pos(1,2), 0.0},                                                    {pos(5,2), 0.0}, {pos(6,2), 1.0},{pos(0,1), 2.0}, {pos(1,1), 0.0}, {pos(2,1), 0.0}, {pos(3,1), 0.0}, {pos(4,1), 0.0}, {pos(5,1), 0.0}, {pos(6,1), 1.0},{pos(0,0), 2.0}, {pos(1,0), 2.0}, {pos(2,0), 1.0}, {pos(3,0), 1.0}, {pos(4,0), 1.0}, {pos(5,0), 0.0}, {pos(6,0), 1.0},};std::unordered_map<U8, float> hurestics_pawn_white = {{pos(0,6), 1.0}, {pos(1,6), 1.7}, {pos(2,6), 1.9}, {pos(3,6), 2.0}, {pos(4,6), 3.0}, {pos(5,6), 0.0}, {pos(6,6), 0.0},{pos(0,5), 1.0}, {pos(1,5), 2.8}, {pos(2,5), 3.0}, {pos(3,5), 3.5}, {pos(4,5), 5.0}, {pos(5,5), 0.0}, {pos(6,5), 0.0},{pos(0,4), 1.0}, {pos(1,4), 2.3},                                                    {pos(5,4), 0.0}, {pos(6,4), 0.0},{pos(0,3), 1.0}, {pos(1,3), 2.0},                                                    {pos(5,3), 0.0}, {pos(6,3), 0.0},{pos(0,2), 0.5}, {pos(1,2), 1.8},                                                    {pos(5,2), 0.0}, {pos(6,2), 0.0},{pos(0,1), 0.5}, {pos(1,1), 1.5}, {pos(2,1), 0.0}, {pos(3,1), 0.0}, {pos(4,1), 0.0}, {pos(5,1), 0.0}, {pos(6,1), 0.0},{pos(0,0), 0.0}, {pos(1,0), 0.0}, {pos(2,0), 0.0}, {pos(3,0), 0.0}, {pos(4,0), 0.0}, {pos(5,0), 0.0}, {pos(6,0), 0.0},};std::unordered_map<U8, float> hurestics_pawn_black = {{pos(0,6), 0.0}, {pos(1,6), 0.0}, {pos(2,6), 0.0}, {pos(3,6), 0.0}, {pos(4,6), 0.0}, {pos(5,6), 0.0}, {pos(6,6), 0.0},{pos(0,5), 0.0}, {pos(1,5), 0.0}, {pos(2,5), 0.0}, {pos(3,5), 0.0}, {pos(4,5), 0.0}, {pos(5,5), 2.5}, {pos(6,5), 0.5},{pos(0,4), 0.0}, {pos(1,4), 0.0},                                                    {pos(5,4), 2.8}, {pos(6,4), 0.5},{pos(0,3), 0.0}, {pos(1,3), 0.0},                                                    {pos(5,3), 2.0}, {pos(6,3), 1.0},{pos(0,2), 0.0}, {pos(1,2), 0.0},                                                    {pos(5,2), 2.3}, {pos(6,2), 1.0},{pos(0,1), 0.0}, {pos(1,1), 0.0}, {pos(2,1), 5.0}, {pos(3,1), 3.5}, {pos(4,1), 3.0}, {pos(5,1), 2.8}, {pos(6,1), 1.0},{pos(0,0), 0.0}, {pos(1,0), 0.0}, {pos(2,0), 3.0}, {pos(3,0), 2.0}, {pos(4,0), 1.9}, {pos(5,0), 1.7}, {pos(6,0), 1.0},};std::unordered_map<U8, float> hurestics_bishop_white = {{pos(0,6), 0.0}, {pos(1,6), 0.0}, {pos(2,6), 0.0}, {pos(3,6), 1.2}, {pos(4,6), 0.0}, {pos(5,6), 0.0}, {pos(6,6), 0.0}, {pos(0,5), 0.0}, {pos(1,5), 0.0}, {pos(2,5), 1.5}, {pos(3,5), 0.0}, {pos(4,5), 1.5}, {pos(5,5), 0.0}, {pos(6,5), 0.0},{pos(0,4), 0.0}, {pos(1,4), 1.7},                                                    {pos(5,4), 1.0}, {pos(6,4), 0.0},{pos(0,3), 1.0}, {pos(1,3), 0.0},                                                    {pos(5,3), 0.0}, {pos(6,3), 0.0},{pos(0,2), 0.0}, {pos(1,2), 2.0},                                                    {pos(5,2), 1.0}, {pos(6,2), 0.0},{pos(0,1), 0.0}, {pos(1,1), 0.0}, {pos(2,1), 2.0}, {pos(3,1), 0.0}, {pos(4,1), 0.0}, {pos(5,1), 0.0}, {pos(6,1), 0.0},{pos(0,0), 0.0}, {pos(1,0), 0.0}, {pos(2,0), 0.0}, {pos(3,0), 1.0}, {pos(4,0), 0.0}, {pos(5,0), 0.0}, {pos(6,0), 0.0},};std::unordered_map<U8, float> hurestics_bishop_black = {{pos(0,6), 0.0}, {pos(1,6), 0.0}, {pos(2,6), 0.0}, {pos(3,6), 1.0}, {pos(4,6), 0.0}, {pos(5,6), 0.0}, {pos(6,6), 0.0},{pos(0,5), 0.0}, {pos(1,5), 0.0}, {pos(2,5), 0.0}, {pos(3,5), 0.0}, {pos(4,5), 2.0}, {pos(5,5), 0.0}, {pos(6,5), 0.0},{pos(0,4), 0.0}, {pos(1,4), 1.0},                                                    {pos(5,4), 2.0}, {pos(6,4), 0.0},{pos(0,3), 0.0}, {pos(1,3), 0.0},                                                    {pos(5,3), 0.0}, {pos(6,3), 1.0},{pos(0,2), 0.0}, {pos(1,2), 1.0},                                                    {pos(5,2), 1.7}, {pos(6,2), 0.0},{pos(0,1), 0.0}, {pos(1,1), 0.0}, {pos(2,1), 1.5}, {pos(3,1), 0.0}, {pos(4,1), 1.5}, {pos(5,1), 0.0}, {pos(6,1), 0.0},{pos(0,0), 0.0}, {pos(1,0), 0.0}, {pos(2,0), 0.0}, {pos(3,0), 1.2}, {pos(4,0), 0.0}, {pos(5,0), 0.0}, {pos(6,0), 0.0},};
float getEvaluation(const Board& b1){
    newcount += 1;
    eval evaluation;
    evaluation.king[0] = 0; evaluation.king[1] = 0; evaluation.bishop[0] = 0; evaluation.bishop[1] = 0; 
    evaluation.rook[0] = 0; evaluation.rook[1] = 0; evaluation.pawn[0] = 0; evaluation.pawn[1] = 0;
    evaluation.bishop_pos[0] = 0; evaluation.bishop_pos[1] = 0; evaluation.rook_pos[0] = 0; evaluation.rook_pos[1] = 0;
    evaluation.pawn_pos[0] = 0; evaluation.pawn_pos[1] = 0; evaluation.check[10] = 0; evaluation.check[1] = 0;

    U8 w_king1 = b1.data.w_king;U8 b_king1 = b1.data.b_king;U8 w_rook_ws1 = b1.data.w_rook_1;U8 w_rook_bs1 = b1.data.w_rook_2;U8 b_rook_ws1 = b1.data.b_rook_1;U8 b_rook_bs1 = b1.data.b_rook_2;U8 w_bishop1 = b1.data.w_bishop;U8 b_bishop1 = b1.data.b_bishop;U8 w_pawn_ws1 = b1.data.w_pawn_1;U8 w_pawn_bs1 = b1.data.w_pawn_2;U8 b_pawn_ws1 = b1.data.b_pawn_1;U8 b_pawn_bs1 = b1.data.b_pawn_2;
    if (w_king1 != DEAD){
        evaluation.king[0] += 1;
    }
    if (b_king1 != DEAD){
        evaluation.king[1] += 1;
    }
    if (w_rook_ws1 != DEAD){
        evaluation.rook[0] += 1;
        evaluation.rook_pos[0] += hurestics_rook_white[w_rook_ws1];
    }
    if (w_rook_bs1 != DEAD){
        evaluation.rook[0] += 1;
        evaluation.rook_pos[0] += hurestics_rook_white[w_rook_bs1];
    }
    if (b_rook_ws1 != DEAD){
        evaluation.rook[1] += 1;
        evaluation.rook_pos[1] += hurestics_rook_black[b_rook_ws1];
    }
    if (b_rook_bs1 != DEAD){
        evaluation.rook[1] += 1;
        evaluation.rook_pos[1] += hurestics_rook_black[b_rook_bs1];
    }
    if (w_bishop1 != DEAD){
        evaluation.bishop[0] += 1;
        evaluation.bishop_pos[0] += hurestics_bishop_white[w_bishop1];
    }
    if (b_bishop1 != DEAD){
        evaluation.bishop[1] += 1;
        evaluation.bishop_pos[1] += hurestics_bishop_black[b_bishop1];
    }
    if (w_pawn_ws1 != DEAD){
        if (b1.data.board_0[w_pawn_ws1] & PAWN){
            evaluation.pawn[0] += 1;
            evaluation.pawn_pos[0] += hurestics_pawn_white[w_pawn_ws1];
        }
        else if (b1.data.board_0[w_pawn_ws1] & BISHOP){
            evaluation.bishop[0] += 1;
            evaluation.bishop_pos[0] += hurestics_bishop_white[w_pawn_ws1];
        }
        else if (b1.data.board_0[w_pawn_ws1] & ROOK){
            evaluation.rook[0] += 1;
            evaluation.rook_pos[0] += hurestics_rook_white[w_pawn_ws1];
        }
    }
    if (w_pawn_bs1 != DEAD){
        if (b1.data.board_0[w_pawn_bs1] & PAWN){
            evaluation.pawn[0] += 1;
            evaluation.pawn_pos[0] += hurestics_pawn_white[w_pawn_bs1];
        }
        else if (b1.data.board_0[w_pawn_bs1] & BISHOP){
            evaluation.bishop[0] += 1;
            evaluation.bishop_pos[0] += hurestics_bishop_white[w_pawn_bs1];
        }
        else if (b1.data.board_0[w_pawn_bs1] & ROOK){
            evaluation.rook[0] += 1;
            evaluation.rook_pos[0] += hurestics_rook_white[w_pawn_bs1];
        }
    }
    if (b_pawn_ws1 != DEAD){
        if (b1.data.board_0[b_pawn_ws1] & PAWN){
            evaluation.pawn[1] += 1;
            evaluation.pawn_pos[1] += hurestics_pawn_black[b_pawn_ws1];
        }
        else if (b1.data.board_0[b_pawn_ws1] & BISHOP){
            evaluation.bishop[1] += 1;
            evaluation.bishop_pos[1] += hurestics_bishop_black[b_pawn_ws1];
        }
        else if (b1.data.board_0[b_pawn_ws1] & ROOK){
            evaluation.rook[1] += 1;
            evaluation.rook_pos[1] += hurestics_rook_black[b_pawn_ws1];
        }
    }
    if (b_pawn_bs1 != DEAD){
        if (b1.data.board_0[b_pawn_bs1] & PAWN){
            evaluation.pawn[1] += 1;
            evaluation.pawn_pos[1] += hurestics_pawn_black[b_pawn_bs1];
        }
        else if (b1.data.board_0[b_pawn_bs1] & BISHOP){
            evaluation.bishop[1] += 1;
            evaluation.bishop_pos[1] += hurestics_bishop_black[b_pawn_bs1];
        }
        else if (b1.data.board_0[b_pawn_bs1] & ROOK){
            evaluation.rook[1] += 1;
            evaluation.rook_pos[1] += hurestics_rook_black[b_pawn_bs1];
        }
    }
    
    float score = weights.king * (evaluation.king[0] - evaluation.king[1]) 
                + weights.bishop * (evaluation.bishop[0] - evaluation.bishop[1]) 
                + weights.rook * (evaluation.rook[0] - evaluation.rook[1]) 
                + weights.pawn * (evaluation.pawn[0] - evaluation.pawn[1])+ (evaluation.bishop_pos[0] - evaluation.bishop_pos[1])+ (evaluation.rook_pos[0] - evaluation.rook_pos[1])+ (evaluation.pawn_pos[0] - evaluation.pawn_pos[1]);
    // std::cout << "Score: " << score << std::endl;
    return score;
}

//Get the captures possible for a given board position - sorted by MVV/LVA (Most valuable victim/Least valuable attacker)
//Basically sort the moves by the value of the capture
std::unordered_set<U16> getCaptures(const Board& b){
    auto moveset = b.get_legal_moves();
    std::map<int, std::unordered_set<U16>, std::greater<int>> capturemap;
    for (auto move : moveset){
        auto p1 = getp1(move);
        if (b.data.board_0[p1] != 0){
            int capturevalue = 0;
            if (b.data.board_0[p1] && BISHOP){
                capturevalue = 6;
            }else if (b.data.board_0[p1] && ROOK){
                capturevalue = 7;
            }else if (b.data.board_0[p1] && PAWN){
                capturevalue = 3;
            }
            auto p0 = getp0(move);
            if (b.data.board_0[p0] && BISHOP){
                capturevalue -= 6;
            }else if (b.data.board_0[p0] && ROOK){
                capturevalue -= 7;
            } else if (b.data.board_0[p0] && PAWN){
                capturevalue -= 3;
            }
            capturemap[capturevalue].insert(move);
        }
    }
    std::unordered_set<U16> captures;
    for (auto it = capturemap.begin(); it != capturemap.end(); it ++){
        for (auto move : it->second){
            captures.insert(move);
        }
        // std::cout << "capture score: " << it->first << std::endl;
    }
    return captures;
}


//Quiescence Search starts here
float quismini(const Board &b, float alpha, float beta, int maxDepth);

float quismaxi(const Board &b, float alpha, float beta, int maxDepth){
    quiscount += 1;
    float eval = getEvaluation(b);
    if (eval >= beta) return beta;
    if (eval > alpha) alpha = eval;

    auto captureset = getCaptures(b);
    if (captureset.size() == 0) return eval;
    if (maxDepth == 0) return eval;
    for (auto capture: captureset){
        Board tempBoard;
        tempBoard.data = b.data;
        tempBoard.do_move_(capture);
        float score = quismini(tempBoard, alpha, beta, maxDepth - 1);
        if (score >= beta) return beta;
        if (score > alpha) alpha = score;
    }
    return alpha;

}

float quismini(const Board &b, float alpha, float beta, int maxDepth){
    quiscount += 1;
    float eval = getEvaluation(b);
    if (eval <= alpha) return alpha;
    if (eval < beta) beta = eval;

    auto captureset = getCaptures(b);
    if (captureset.size() == 0) return eval;
    if (maxDepth == 0) return eval;
    for (auto capture: captureset){
        Board tempBoard;
        tempBoard.data = b.data;
        tempBoard.do_move_(capture);
        float score = quismaxi(tempBoard, alpha, beta, maxDepth - 1);
        if (score <= alpha) return alpha;
        if (score < beta) beta = score;
    }
    return beta;
}
//Quiescence Search ends here

//Minimaxi with alpha beta pruning starts here
float mini(float alpha, float beta, int depth, const Board& b, unsigned long long starttime, int time_avail);

float maxi(float alpha, float beta, int depth, const Board& b, unsigned long long starttime, int time_avail){
    std::cout << "Chilling in maxi" << std::endl;
    auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
    if ((currtime- starttime) >= time_avail) return beta;

    float adjustment = 0;
    // std::cout << "history stack size: " << historyStack.size() << std::endl;
    // if (historyStack.size() >= 2 && historyStack[historyStack.size() - 2] == transpositionTable.findhash(b)){
    //     std::cout << "draw detected" << std::endl;
    //     drawdetections ++;
    //     adjustment = contemptFactor;
    // }

    if (depth == 0) return quismaxi(b, alpha, beta, 3) + adjustment;

    auto moveset = b.get_legal_moves();
    if (moveset.size() == 0) {
        if (b.in_check()) return -INT_MAX;
        return 0 + adjustment;
    }
    if (transpositionTable.exists(b)){
        fetchcount += 1;
        auto entry = transpositionTable.getEntry(b);
        if (entry->depth >= depth){
            if (entry->type == 0){
                return entry->eval + adjustment;
            }else if (entry->type == 1){
                if (entry->eval >= beta){
                    return beta; //no need for contempt factor if cutoff is there
                }
            }
        }
    }
    U16 currbestmove;
    // std::vector<U16> localpv;
    // historyStack.push_back(transpositionTable.findhash(b));
    // if (pv->size() > 0) std::cout << "pv size: " << pv->size() << std::endl;
    // if (pv->size() > 0){
    //     Board tempBoard = b;
    //     U16 move = pv->back();
    //     tempBoard.do_move(move);
    //     pv->pop_back();
    //     float score = mini(alpha, beta, depth-1, tempBoard, pv);
    //     if (score > alpha){
    //         alpha = score;
    //     }
    //     if (alpha >= beta){
    //         transpositionTable.insert(b, depth, 1, alpha);
    //         historyStack.pop_back();
    //         return beta; //no need for contempt factor if cutoff is there
    //     }
    // }
    for (auto move : moveset){
        Board tempBoard;
        tempBoard.data = b.data;

        tempBoard.do_move_(move);
        // std::vector<U16> temp;
        float score = mini(alpha, beta, depth-1, tempBoard, starttime, time_avail);
        auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        if (currtime - starttime >= time_avail) return beta; //if search has been stopped, return beta
        // std::cout << "state score: " << score << std::endl;
        if (score > alpha){
            alpha = score;
            currbestmove = move;
            // temp.push_back(move);
            // localpv = temp;
            // for (auto u: historyStack){
            //     std::cout << u << " ";
            // }
            // std::cout << std::endl;
        }
        if (alpha >= beta){
            transpositionTable.insert(b, depth, 1, alpha);
            // historyStack.pop_back();
            return beta; //no need for contempt factor if cutoff is there
        }
    }
    // *pv = localpv;
    // historyStack.pop_back();
    transpositionTable.insert(b, depth, 0, alpha, currbestmove);
    return alpha; // contempt factor would have already been accounted for in the child nodes

}

float mini(float alpha, float beta, int depth, const Board& b, unsigned long long starttime, int time_avail){
    auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
    std::cout << "currtime: " << currtime << " starttime: " << starttime << " time_avail: " << time_avail << std::endl;
    if (currtime - starttime >= time_avail) return alpha;
    float adjustment = 0;
    // std::cout << "history stack size: " << historyStack.size() << std::endl;
    // if (historyStack.size() >= 2 && historyStack[historyStack.size() - 2] == transpositionTable.findhash(b)){
    //     std::cout << "draw detected" << std::endl;
    //     drawdetections ++;
    //     adjustment = contemptFactor;
    // }

    if (depth == 0) return quismini(b, alpha, beta, 3) + adjustment;
    auto moveset = b.get_legal_moves();
    if (moveset.size() == 0){
        if (b.in_check()) return INT_MAX;
        return 0 + adjustment;
    }
    if (transpositionTable.exists(b)){
        fetchcount += 1;
        auto entry = transpositionTable.getEntry(b);
        if (entry->depth >= depth){
            if (entry->type == 0){
                return entry->eval + adjustment;
            }else if (entry->type == 2){
                if (entry->eval <= alpha){
                    return alpha; //no need for contempt factor if cutoff is there
                }
            }
        }
    }
    // std::vector<U16> localpv;
    U16 currbestmove;
    // historyStack.push_back(transpositionTable.findhash(b));
    // if (pv->size() > 0) std::cout << "pv size: " << pv->size() << std::endl;
    // if (pv->size() > 0){
    //     Board tempBoard = b;
    //     U16 move = pv->back();
    //     tempBoard.do_move(move);
    //     pv->pop_back();
    //     float score = maxi(alpha, beta, depth-1, tempBoard, pv);
    //     if (score < beta){
    //         beta = score;
    //     }
    //     if (alpha >= beta){
    //         transpositionTable.insert(b, depth, 2, beta);
    //         historyStack.pop_back();
    //         return alpha; //no need for contempt factor if cutoff is there
    //     }
    // }
    for (auto move : moveset){
        Board tempBoard;
        tempBoard.data = b.data;
        tempBoard.do_move_(move);
        // std::vector<U16> temp;
        float score = maxi(alpha, beta, depth-1, tempBoard, starttime, time_avail);
        auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
        if (currtime - starttime >= time_avail) return alpha; //if search has been stopped, return alpha 
        // std::cout << "state score: " << score << std::endl;
        if (score < beta){
            beta = score;
            currbestmove = move;
            // temp.push_back(move);
            // localpv = temp;
        }
        if (alpha >= beta){
            transpositionTable.insert(b, depth, 2, beta);
            // historyStack.pop_back();
            return alpha;
        }
    }
    // *pv = localpv;
    // historyStack.pop_back();
    transpositionTable.insert(b, depth, 0, beta, currbestmove);
    return beta; // contempt factor would have already been accounted for in the child nodes
}

int getGamePhase(const Board& b){
    int btype = b.data.board_type;
    if (btype == 1){ // 7-3
        // phase = 0 -> if more than equal to 5 peices of both sides
        // phase = 1 -> if more than equal to 3 peices of both sides
        // phase = 2 -> otherwise
        int peices_white = 0; int peices_black = 0;
        if (b.data.w_king != DEAD) peices_white += 1;
        if (b.data.w_rook_1 != DEAD) peices_white += 1;
        if (b.data.w_rook_2 != DEAD) peices_white += 1;
        if (b.data.w_bishop != DEAD) peices_white += 1;
        if (b.data.w_pawn_1 != DEAD) peices_white += 1;
        if (b.data.w_pawn_2 != DEAD) peices_white += 1;
        if (b.data.b_king != DEAD) peices_black += 1;
        if (b.data.b_rook_1 != DEAD) peices_black += 1;
        if (b.data.b_rook_2 != DEAD) peices_black += 1;
        if (b.data.b_bishop != DEAD) peices_black += 1;
        if (b.data.b_pawn_1 != DEAD) peices_black += 1;
        if (b.data.b_pawn_2 != DEAD) peices_black += 1;
        if (peices_white >= 5 && peices_black >= 5){
            return 0;
        }else if (peices_white >= 3 && peices_black >= 3){
            return 1;
        }else{
            return 2;
        }

    }else if (btype == 2){ // 8-2
        // phase = 0 -> if more than equal to 7 peices of both sides
        // phase = 1 -> if more than equal to 4 peices of both sides
        // phase = 2 -> otherwise
        int peices_white = 0; int peices_black = 0;
        if (b.data.w_king != DEAD) peices_white += 1;
        if (b.data.w_rook_1 != DEAD) peices_white += 1;
        if (b.data.w_rook_2 != DEAD) peices_white += 1;
        if (b.data.w_bishop != DEAD) peices_white += 1;
        if (b.data.w_pawn_1 != DEAD) peices_white += 1;
        if (b.data.w_pawn_2 != DEAD) peices_white += 1;
        if (b.data.w_pawn_3 != DEAD) peices_white += 1;
        if (b.data.w_pawn_4 != DEAD) peices_white += 1;
        if (b.data.b_king != DEAD) peices_black += 1;
        if (b.data.b_rook_1 != DEAD) peices_black += 1;
        if (b.data.b_rook_2 != DEAD) peices_black += 1;
        if (b.data.b_bishop != DEAD) peices_black += 1;
        if (b.data.b_pawn_1 != DEAD) peices_black += 1;
        if (b.data.b_pawn_2 != DEAD) peices_black += 1;
        if (b.data.b_pawn_3 != DEAD) peices_black += 1;
        if (b.data.b_pawn_4 != DEAD) peices_black += 1;
        if (peices_white >= 7 && peices_black >= 7){
            return 0;
        }else if (peices_white >= 4 && peices_black >= 4){
            return 1;
        }else{
            return 2;
        }
    }else if (btype == 3){ // 8-4
        // phase = 0 -> if more than equal to 9 peices of both sides
        // phase = 1 -> if more than equal to 4 peices of both sides
        // phase = 2 -> otherwise
        int peices_white = 0; int peices_black = 0;
        if (b.data.w_king != DEAD) peices_white += 1;
        if (b.data.w_rook_1 != DEAD) peices_white += 1;
        if (b.data.w_rook_2 != DEAD) peices_white += 1;
        if (b.data.w_bishop != DEAD) peices_white += 1;
        if (b.data.w_knight_1 != DEAD) peices_white += 1;
        if (b.data.w_knight_2 != DEAD) peices_white += 1;
        if (b.data.w_pawn_1 != DEAD) peices_white += 1;
        if (b.data.w_pawn_2 != DEAD) peices_white += 1;
        if (b.data.b_king != DEAD) peices_black += 1;
        if (b.data.b_rook_1 != DEAD) peices_black += 1;
        if (b.data.b_rook_2 != DEAD) peices_black += 1;
        if (b.data.b_bishop != DEAD) peices_black += 1;
        if (b.data.b_knight_1 != DEAD) peices_black += 1;
        if (b.data.b_knight_2 != DEAD) peices_black += 1;
        if (b.data.b_pawn_1 != DEAD) peices_black += 1;
        if (b.data.b_pawn_2 != DEAD) peices_black += 1;
        if (peices_white >= 9 && peices_black >= 9){
            return 0;
        }else if (peices_white >= 4 && peices_black >= 4){
            return 1;
        }else{
            return 2;
        }
    }
}

int moves_phase = 0; //keeps track of the number of moves played yet

std::pair<int,int> allot_depth_time(int gamephase, const Board& b, int time_left){
    int btype = b.data.board_type;
    if (btype == 1){ // 7-3 
        if (gamephase == 0){
            double total_time_phase = 120*0.2*1000; //milliseconds
            int avgmoves = 4;
            return std::make_pair(5, std::min(total_time_phase/avgmoves, time_left*0.05));
        } else if (gamephase == 1){
            double total_time_phase = 120*0.4*1000; //milliseconds
            int avgmoves = 25;
            return std::make_pair(6, std::min(total_time_phase/avgmoves, time_left*0.03));
        } else if (gamephase == 2){
            double total_time_phase = 120*0.4*1000; //milliseconds
            int avgmoves = 12;
            return std::make_pair(9, std::min(total_time_phase/avgmoves, time_left*0.15));
        }
    // } else if (btype == 2){ // 8-2

    // } else if (btype == 3){ // 8-4

    }
}


//Minimaxi with alpha beta pruning ends here
// U16 firstmove(PlayerColor c, const Board& b1){Board* bp = new Board();Board b = *bp;if (c == WHITE){if (b1.data.w_king == b.data.w_king && b1.data.w_rook_1 == b.data.w_rook_1 && b1.data.w_rook_2 == b.data.w_rook_2 && b1.data.w_bishop == b.data.w_bishop && b1.data.w_pawn_1 == b.data.w_pawn_1 && b1.data.w_pawn_2 == b.data.w_pawn_2){delete bp; return move(pos(2,1), pos(1,2));}}else{if (b1.data.b_king == b.data.b_king && b1.data.b_rook_1 == b.data.b_rook_1 && b1.data.b_rook_2 == b.data.b_rook_2 && b1.data.b_bishop == b.data.b_bishop && b1.data.b_pawn_1 == b.data.b_pawn_1 && b1.data.b_pawn_2 == b.data.b_pawn_2){delete bp; return move(pos(4,5), pos(5,4));}}delete bp; return 0;}
void Engine::find_best_move(const Board& b) {
    // historyStack.push_back(transpositionTable.findhash(b));
    // searchstatus = &search;
    unsigned long long starttime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
    // U16 firstMove = firstmove(b.data.player_to_play, b);if (firstMove){this->best_move = firstMove;return;}
    auto moveset = b.get_legal_moves();
    int curr_phase = getGamePhase(b);
    std::pair<int,int> depth_time = allot_depth_time(curr_phase, b, this->time_left.count());


    if (moveset.size() == 0) {
        this->best_move = 0;
    }
    else {
        if (b.data.player_to_play == WHITE){
            float bestScore = -INT_MAX;
            // std::vector<U16> pv;
            std::cout << "depth first: " << depth_time.first << std::endl;
            for (int currdepth = 1; currdepth <= depth_time.first; currdepth ++){
                std::cout << "currdepth: " << currdepth << std::endl;
                auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
                if ((currtime - starttime) >= depth_time.second) {
                    maxdepth = std::max(maxdepth, currdepth - 1);
                    std::cout << "breaking1: " << currtime << " " << starttime << " " << depth_time.second << std::endl;
                    // std::cout << "eval till depth: " << currdepth - 1 << std::endl;
                    break;
                }
                if (transpositionTable.exists(b) && transpositionTable.getEntry(b)->move != 0 && transpositionTable.getEntry(b)->depth >= currdepth){
                    std::cout << "wow" << std::endl;
                    fetchcount += 1;
                    this->best_move = transpositionTable.getEntry(b)->move;
                } else {
                    std::cout << "yess" << std::endl;
                    newcount += 1;
                    bestScore = -INT_MAX;
                    //try out the principal variation first
                    // if (pv.size() > 0){
                    //     Board* tempBoard = b.copy();
                    //     tempBoard->do_move(pv.back());
                    //     pv.pop_back();
                    //     float score = mini(bestScore, INT_MAX, currdepth - 1, *tempBoard, &pv);
                    //     if (score > bestScore){
                    //         bestScore = score;
                    //     }
                    //     pv.clear();
                    //     delete tempBoard;
                    // }
                    if (this->best_move && currdepth >= 2){
                        Board tempBoard;
                        tempBoard.data = b.data;
                        // std::cout << "Tempboard check #1: " << board_to_str(&(tempBoard.data)) << std::endl;
                        tempBoard.do_move_(this->best_move);
                        float score = mini(bestScore, INT_MAX, currdepth - 1, tempBoard, starttime, depth_time.second);
                        if (score > bestScore){
                            bestScore = score;
                        }
                    }
                    for (auto moves: moveset){
                    auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
                    if ((currtime - starttime) >= depth_time.second) {
                            maxdepth = std::max(maxdepth, currdepth - 1);
                            std::cout << "breaking2: " << currtime << " " << starttime << " " << depth_time.second << std::endl;
                            // std::cout << "eval till depth: " << currdepth - 1 << std::endl;
                            break;
                        }
                        Board tempBoard;
                        tempBoard.data = b.data;
                        // std::cout << "Tempboard check #1: " << board_to_str(&(tempBoard.data)) << std::endl;

                        tempBoard.do_move_(moves);
                        // std::vector<U16> temp;
                        float score = mini(bestScore, INT_MAX, currdepth - 1, tempBoard, starttime, depth_time.second);
                        if (score > bestScore){
                            bestScore = score;
                            this->best_move = moves;
                            // temp.push_back(moves);
                            // pv = temp;
                        }
                    }
                    auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
                    if ((currtime - starttime) < depth_time.second) transpositionTable.insert(b, currdepth, 0, bestScore, this->best_move);
                }
                std::cout << "time elapsed: " << currtime - starttime << std::endl;
            }
            // std::cout << "New positions: " << newcount << std::endl;
            // std::cout << "Transposition positions: " << fetchcount << std::endl;
            // std::cout << "Quiescence positions: " << quiscount << std::endl;
            // std::cout << "Draw detections: " << drawdetections << std::endl;
            // std::cout << "Max depth: " << maxdepth << std::endl;
        }else{
            float bestScore = INT_MAX;
            // std::vector<U16> pv;
            std::cout << "depth first: " << depth_time.first << std::endl;
            for (int currdepth = 1; currdepth <= depth_time.first; currdepth ++){
                std::cout << "currdepth: " << currdepth << std::endl;
                auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
                if ((currtime - starttime) >= depth_time.second) {
                    // std::cout << "eval till depth: " << currdepth - 1 << std::endl;
                    maxdepth = std::max(maxdepth, currdepth - 1);
                    std::cout << "breaking3: " << currtime << " " << starttime << " " << depth_time.second << std::endl;
                    break;
                }
                if (transpositionTable.exists(b) && transpositionTable.getEntry(b)->move != 0 && transpositionTable.getEntry(b)->depth >= currdepth){
                    fetchcount += 1;
                    this->best_move = transpositionTable.getEntry(b)->move;
                } else {
                    newcount += 1;
                    bestScore = INT_MAX;
                    //try out the principal variation first
                    // if (pv.size() > 0){
                    //     Board* tempBoard = b.copy();
                    //     tempBoard->do_move(pv.back());
                    //     pv.pop_back();
                    //     float score = maxi(-INT_MAX, bestScore, currdepth - 1, *tempBoard, &pv);
                    //     if (score < bestScore){
                    //         bestScore = score;
                    //     }
                    //     pv.clear();
                    //     delete tempBoard;
                    // }
                    if (this->best_move && currdepth >= 2){
                        Board tempBoard;
                        tempBoard.data = b.data;
                        // std::cout << "Tempboard check #1: " << board_to_str(&(tempBoard.data)) << std::endl;
                        tempBoard.do_move_(this->best_move);
                        float score = maxi(-INT_MAX, bestScore, currdepth - 1, tempBoard, starttime, depth_time.second);
                        if (score < bestScore){
                            bestScore = score;
                        }
                    }
                    for (auto moves: moveset){
                    auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
                    if ((currtime - starttime) >= depth_time.second) {
                            maxdepth = std::max(maxdepth, currdepth - 1);
                            // std::cout << "eval till depth: " << currdepth - 1 << std::endl;
                            std::cout << "breaking4: " << currtime << " " << starttime << " " << depth_time.second << std::endl;
                            break;
                        }
                        Board tempBoard;
                        tempBoard.data = b.data;
                        // std::cout << "Tempboard check #1: " << board_to_str(&(tempBoard.data)) << std::endl;
                        tempBoard.do_move_(moves);
                        float score = maxi(-INT_MAX, bestScore, currdepth - 1, tempBoard, starttime, depth_time.second);
                        if (score < bestScore){
                            bestScore = score;
                            this->best_move = moves;
                            // pv = temp;
                        }
                    }
                    auto currtime = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
                    if ((currtime - starttime) < depth_time.second) transpositionTable.insert(b, currdepth, 0, bestScore, this->best_move);
                }
                std::cout << "time elapsed: " << currtime - starttime << std::endl;
            }
            // std::cout << "New positions: " << newcount << std::endl;
            // std::cout << "Transposition positions: " << fetchcount << std::endl;
            // std::cout << "Quiescence positions: " << quiscount << std::endl;
            // std::cout << "Draw detections: " << drawdetections << std::endl;
            // std::cout << "Max depth: " << maxdepth << std::endl;
        }
    }
    std::cout << "Time left initially: " << this->time_left.count() << std::endl;
    std::cout << "Total time allotted for move: " << depth_time.second << std::endl;
    std::cout << "Total time used for move: " << std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count() - starttime << std::endl;
    // historyStack.pop_back();
}
