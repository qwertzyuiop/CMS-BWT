#include "CMS-BWT.h"

void constructISA(int32_t *sa, uint32_t *isa, uint32_t n){
   //fprintf(stderr,"\tComputing ISA...\n");
   std::cerr << "\tComputing ISA..." << std::endl;
   for(uint32_t i=0; i<n; i++){
      isa[sa[i]] = i;
   }
}

std::pair<int,int> adjustInterval(int lo, int hi, int offset) {
  int psv = _rmq->psv(lo,offset);
  if(psv == -1){
    psv = 0;
  }else{
    //psv++;
  }
  int nsv = _rmq->nsv(hi+1,offset);
  if(nsv == -1){
    nsv = _n-1;
  }else{
    nsv--;
  }
  return {psv,nsv};
}

std::pair<int,int> fasterContractLeft(int lo, int hi, int offset){
   uint32_t sufhi = _SA[hi];
   uint32_t tmplo = _ISA[lo+1];
   uint32_t tmphi = _ISA[sufhi+1];
   return adjustInterval(tmplo, tmphi, offset);
}

std::pair<int,int> contractLeft(int lo, int hi, int offset){
   uint32_t suflo = _SA[lo];
   uint32_t sufhi = _SA[hi];
   if(suflo == _n-1 || sufhi == _n-1){ //if true we must be at depth 1
      return std::make_pair(0,_n-1); //root
   }
   uint32_t tmplo = _ISA[suflo+1];
   uint32_t tmphi = _ISA[sufhi+1];
   return adjustInterval(tmplo, tmphi, offset);
}

void computeMSFactorAt(const std::string &_sx, filelength_type i, uint32_t *pos, uint32_t *len, int32_t & leftB, int32_t & rightB, bool & isSmallerThanMaxMatch, unsigned char &mismatchingSymbol) {
  uint32_t offset = *len;
  filelength_type j = i + offset;

  int32_t nlb = leftB, nrb = rightB, maxMatch;
  unsigned int match = _SA[nlb];
  while (j < _sn) { // scans the string from j onwards until a maximal prefix is
                    // found between _x and _sx
    if (nlb == nrb) {
      if (_x[_SA[nlb] + offset] != _sx[j]) {
        isSmallerThanMaxMatch = (_x[_SA[nlb] + offset] > _sx[j]);
        mismatchingSymbol = _sx[j];
        break;
      }
      leftB = nlb;
      rightB = nrb;
      maxMatch = nlb;
    } else { // refining the bucket in which the match is found, from left and
             // then from right
      nlb = binarySearchLB(nlb, nrb, offset, _sx[j]);
      if (nlb < 0) {
        // no match, the game is up
        maxMatch = -nlb - 1;
        isSmallerThanMaxMatch = true;
        mismatchingSymbol = _sx[j];
        if (maxMatch == nrb + 1) {
          maxMatch--;
          isSmallerThanMaxMatch = false;
        }

        match = _SA[maxMatch];
        break;
      }
      nrb = binarySearchRB(nlb, nrb, offset, _sx[j]);
      leftB = nlb;
      rightB = nrb;
    }
    match = _SA[nlb];
    j++;
    offset++;
  }
  *pos = match;
  *len = offset;
}

//Returns the leftmost occurrence of the element if it is present or (if not present)
//then returns -(x+1) where x is the index at which the key would be inserted into the
//array: i.e., the index of the first element greater than the key, or hi+1 if all elements
//in the array are less than the specified key.
inline int32_t binarySearchLB(int32_t lo, int32_t hi, uint32_t offset, data_type c) {
  int32_t low = lo, high = hi;
  while (low <= high) {
    int32_t mid = (low + high) >> 1;
    data_type midVal = _x[_SA[mid] + offset];
    if (midVal < c){
      low = mid + 1;
      __builtin_prefetch(&_x[_SA[(low + high) >> 1] + offset], 0, 0);
    }
    else if (midVal > c){
      high = mid - 1;
      __builtin_prefetch(&_x[_SA[(low + high) >> 1] + offset], 0, 0);
    }
    else { //midVal == c
      if (mid == lo)
        return mid; // leftmost occ of key found
      data_type midValLeft = _x[_SA[mid - 1] + offset];
      if (midValLeft == midVal) {
        high = mid - 1; //discard mid and the ones to the right of mid
        __builtin_prefetch(&_x[_SA[(low + high) >> 1] + offset], 0, 0);
      } else { //midValLeft must be less than midVal == c
        return mid; //leftmost occ of key found
      }
    }
  }
  return -(low + 1);  // key not found.
}


inline int32_t binarySearchRB(int32_t lo, int32_t hi, uint32_t offset, data_type c) {
  int32_t low = lo, high = hi;
  while (low <= high) {
    int32_t mid = (low + high) >> 1;
    data_type midVal = _x[_SA[mid] + offset];
    if (midVal < c){
      low = mid + 1;
      __builtin_prefetch(&_x[_SA[(low + high) >> 1] + offset], 0, 0);
    }
    else if (midVal > c){
      high = mid - 1;
      __builtin_prefetch(&_x[_SA[(low + high) >> 1] + offset], 0, 0);
    }
    else { //midVal == c
      if (mid == hi)
        return mid; // rightmost occ of key found
      data_type midValRight = _x[_SA[mid + 1] + offset];
      if (midValRight == midVal) {
        low = mid + 1; //discard mid and the ones to the left of mid
        __builtin_prefetch(&_x[_SA[(low + high) >> 1] + offset], 0, 0);
      } else { //midValRight must be greater than midVal == c
        return mid; //rightmost occ of key found
      }
    }
  }
  return -(low + 1);  // key not found.
}

void initialize_reference(Args arg, std::string &refFileName, std::string &collFileName,
  uint64_t prefixLength) {
  auto t1 = std::chrono::high_resolution_clock::now();
  errno = 0;
  FILE *infileRef = fopen(refFileName.c_str(), "r");
  if (!infileRef) {
    std::cerr << "Error opening file of base sequence " << refFileName
    << ", errno=" << errno << '\n';
    exit(1);
  }
  std::cerr << "About to read ref\n";

  unsigned int n = 0;
  fseek(infileRef, 0, SEEK_END);
  n = ftell(infileRef) / sizeof(data_type);
  std::cerr << "n = " << n << '\n';
  fseek(infileRef, 0, SEEK_SET);
  if (n) {
    char firstChar;
    int o = fread(&firstChar, sizeof(char), 1, infileRef);
    if (firstChar == '>') {
        _x.reserve(n);
        std::ifstream streamInfileRef(refFileName);
        std::string line, content;
        while (std::getline(streamInfileRef, line).good()) {
          if (line.empty() || line[0] == '>') {
              _x += content;
              std::string().swap(content);
          } else if (!line.empty()) {
              content += line;
          }
        }
        if (content.size()) {
          _x += content;
        }

        std::string().swap(content);
        _x.shrink_to_fit();
        streamInfileRef.close();
    } else {
        fseek(infileRef, 0, SEEK_SET);
        _x.resize(n);
        if (n != fread(&_x[0], sizeof(data_type), n, infileRef)) {
          std::cerr << "Error reading " << n << " bytes from file " << refFileName
              << '\n';
          exit(1);
        }
        _x.shrink_to_fit();
    }
  } else {
    std::cerr << "Reference file is empty!\n";
    exit(1);
  }
  fclose(infileRef);
  std::cerr << "Reference (size = " << _x.size() << "):\n\t";

  auto t01 = std::chrono::high_resolution_clock::now();
  if ((_x[_x.size() - 1] == '\n') | (_x[_x.size() - 1] == '\r') | (_x[_x.size() - 1] == 0)) {
    _x.erase(_x.size() - 1);
  }
  if (_x[_x.size() - 1] == '$') {
    _x.erase(_x.size() - 1);
  }

  FILE *infile = fopen(collFileName.c_str(), "r");
  if (!infile) {
    std::cerr << "Error opening file of sequence (" << collFileName << ")\n";
    exit(1);
  }
  filelength_type sn = 0;
  fseek(infile, 0L, SEEK_END);
  std::cerr << "ftello(infile): " << ftello(infile) << '\n';
  sn = std::min(ftello(infile) / sizeof(data_type), prefixLength);
  std::cerr << "sn: " << sn << '\n';
  fclose(infile);
  _sn = sn;

  // augmenting the reference with Ns and other characters
  //  if(_x.find('N') == std::string::npos) _x.append((int)_x.size()*0.05, 'N');

  for (uint16_t i = 3; i < sizeChars / 2; i++) {
    if (_x.find((char)i) == std::string::npos)
        _x.append(1, (data_type)i);
  }

  _x += (char)1;
  _x += (char)0;

  auto t02 = std::chrono::high_resolution_clock::now();
  std::cerr << "Augmenting reference done in "
  << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01)
    .count()
  << " ms\n";

  t01 = std::chrono::high_resolution_clock::now();
  int32_t *sa = new int32_t[_x.size()];
  libsais(reinterpret_cast<unsigned char *>(const_cast<char *>(_x.c_str())), sa, _x.size(), 0, NULL);
  t02 = std::chrono::high_resolution_clock::now();
  std::cerr << "Computing SA done in "
  << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01)
    .count()
  << " ms\n";

  _n = _x.size();

  t01 = std::chrono::high_resolution_clock::now();
  _SA = sa;
  _ISA = new uint32_t[_n];
  _PLCP = new int32_t[_n];
  _LCP = new int32_t[_n + 1];
  _LCP[_n] = -1;
  t01 = std::chrono::high_resolution_clock::now();
  constructISA(_SA, _ISA, _n);
  t02 = std::chrono::high_resolution_clock::now();
  std::cerr << "Computing ISA done in "
  << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01)
    .count()
  << " ms\n";

  libsais_plcp(reinterpret_cast<unsigned char *>(const_cast<char *>(_x.c_str())), _SA, _PLCP, _x.size());
  libsais_lcp(_PLCP, _SA, _LCP, _x.size());
  for (uint32_t i = 0; i < _n; i++) {
    _PLCP[i] = std::max(_LCP[_ISA[i]], _LCP[_ISA[i] + 1]);
  }
  t02 = std::chrono::high_resolution_clock::now();
  std::cerr << "Computing LCP and PLCP done in "
    << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01)
        .count()
    << " ms\n";

  t01 = std::chrono::high_resolution_clock::now();
  // fprintf(stderr,"\tComputing RMQ...\n");
  std::cerr << "Computing RMQ...\n";
  _rmq = new rmq_tree((int *)_LCP, _n, 7);
  t02 = std::chrono::high_resolution_clock::now();
  std::cerr << "Computing RMQ done in "
  << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01)
    .count()
  << " ms\n";

  t01 = std::chrono::high_resolution_clock::now();
  // fprintf(stderr,"\tComputing BWT...\n");
  std::cerr << "Computing BWT...\n";
  _BWT = new uint8_t[_n];
  for (uint32_t i = 0; i < _n; i++) {
    _BWT[i] = _SA[i] > 0 ? _x[_SA[i] - 1] : char(0);
  }
  t02 = std::chrono::high_resolution_clock::now();
  std::cerr << "Computing BWT done in "
  << std::chrono::duration_cast<std::chrono::milliseconds>(t02 - t01)
    .count()
  << " ms\n";

  std::cerr << "Finished pre-processing\n";

  auto t2 = std::chrono::high_resolution_clock::now();
  uint64_t preprocTime =
  std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
  std::cerr << "Preprocessing done in " << preprocTime << " ms\n";
}

void process_collection_small_reference(Args arg, std::string &collFileName) {
  std::cerr << "File is in memory\n";
  std::cerr << "_x.len: " << _n << '\n';
  std::cerr << "_sx.len: " << _sn << '\n';
  auto t1 = std::chrono::high_resolution_clock::now();

  std::cerr << "About to start main parsing loop...\n";

  uint32_t ndoc = 1;
  int64_t *bucketsForExpandedBWT = new int64_t[_n]();
  bucketsForExpandedBWT[_n - 1] = 0;

  uint64_t i = 0;

  uint64_t maxValue = 0;
  std::vector<uint8_t> listOfChars;

  std::ifstream streamInfile(collFileName, std::ios::in);
  std::string line, content;
  content.reserve(_n * 2);
  uint64_t charactersRead = 0;
  uint32_t headNumber = 0;

  std::vector<std::map<MatchInSet, ItemMatchInSet>> phrasesSet;
  phrasesSet.resize(_n);
  std::vector<uint16_t> nextHead;
  nextHead.reserve(2000000);

  uint64_t capPhrasesVector = 1000000000 / (sizeof(MatchInVectorBigger));
  std::vector<MatchInVectorBigger> phrasesVector;
  phrasesVector.reserve(capPhrasesVector);
  while (std::getline(streamInfile, line).good()) {
    if (line.empty() || line[0] == '>') {
      content += sequenceSeparator;
      charactersRead++;
      int64_t i = 0;
      int32_t leftB = 0;
      int32_t rightB = _n - 1;
      bool isSmallerThanMatch;
      unsigned char mismatchingSymbol;
      uint64_t prevPos = -2;
      uint32_t pos = _n - 1, len = 0;
      uint32_t iCurrentDoc = 0;
      D++;
      while (i < ((int64_t)content.size()) - 1) {
        computeMSFactorAt(content, i, &pos, &len, leftB, rightB,
                          isSmallerThanMatch, mismatchingSymbol);
        if (pos != prevPos + 1) {
          phrasesVector.push_back(MatchInVectorBigger(
              iCurrentDoc, pos, len, isSmallerThanMatch, headNumber));
          headNumber++;
          if (i == 0)
            listOfChars.push_back(sequenceSeparator);
          else
            listOfChars.push_back(content[i - 1]);
          if (bucketsForExpandedBWT[pos] > 0)
            bucketsForExpandedBWT[pos] = -bucketsForExpandedBWT[pos] - 1;
          else
            bucketsForExpandedBWT[pos]--;
        } else {
          if (bucketsForExpandedBWT[pos] >= 0)
            bucketsForExpandedBWT[pos]++;
          else
            bucketsForExpandedBWT[pos]--;
        }
        iCurrentDoc++;
        len--;

        if (leftB == rightB) {
          while (len > _PLCP[pos + 1]) {
            i++;
            iCurrentDoc++;
            len--;
            pos++;
            if (bucketsForExpandedBWT[pos] >= 0)
              bucketsForExpandedBWT[pos]++;
            else
              bucketsForExpandedBWT[pos]--;
          }
          std::pair<int, int> interval =
              adjustInterval(_ISA[pos + 1], _ISA[pos + 1], len);
          leftB = interval.first;
          rightB = interval.second;
        } else {
          std::pair<int, int> interval = contractLeft(leftB, rightB, len);
          leftB = interval.first;
          rightB = interval.second;
        }
        i++;
        prevPos = pos;
      }
      len = 0;
      pos = _n - 1;
      phrasesVector.push_back(
          MatchInVectorBigger(iCurrentDoc, pos, len, 0, headNumber));
      headNumber++;
      bucketsForExpandedBWT[pos]--;
      if (maxValue < iCurrentDoc)
        maxValue = iCurrentDoc;
      iCurrentDoc = 0;
      ndoc++;
      if (i == 0) {
        listOfChars.push_back(sequenceSeparator);
      } else {
        listOfChars.push_back(content[content.size() - 2]);
      }
      content.erase();
      if (phrasesVector.size() >= capPhrasesVector) {
        uint32_t j = 0;
        for (uint32_t i = 0; i < phrasesVector.size() - 1; i++) {
          while (phrasesVector[j].start + phrasesVector[j].len <=
                     phrasesVector[i].start + phrasesVector[i].len &
                 phrasesVector[j].len != 0)
            j++;
          phrasesVector[i].toNext =
              phrasesVector[i].len > 0
                  ? phrasesVector[i + 1].start - phrasesVector[i].start - 1
                  : 0;
          // get ISA next phrase
          phrasesVector[i].start =
              _ISA[phrasesVector[j].pos +
                   (phrasesVector[i].start + phrasesVector[i].len -
                    phrasesVector[j].start)];
          nextHead.push_back(j - i);
          if (phrasesVector[i].len == 0) {
            j++;
          }
        }
        nextHead.push_back(0);
        phrasesVector[phrasesVector.size() - 1].start = 0;

        std::sort(phrasesVector.begin(), phrasesVector.end(),
                  [](const MatchInVectorBigger &headA,
                     const MatchInVectorBigger &headB) {
                    return (headA.pos < headB.pos) * (headA.pos != headB.pos) +
                           (headA.idx < headB.idx) * (headA.pos == headB.pos);
                  });
        
        for (uint32_t i = 0; i < phrasesVector.size(); i++) {
          auto M = MatchInSet(phrasesVector[i].len, phrasesVector[i].smaller,
                              phrasesVector[i].start);
          auto IM =
              ItemMatchInSet(phrasesVector[i].toNext, phrasesVector[i].idx);
          auto inserted = phrasesSet[phrasesVector[i].pos].insert(
              std::pair<MatchInSet, ItemMatchInSet>{M, IM});
          if (!inserted.second) {
            inserted.first->second.addIdx(phrasesVector[i].idx);
          }
        }
        phrasesVector.clear();
      }
    } else if (!line.empty()) {
      charactersRead += line.size();
      if (charactersRead >=
          _sn - 1) { // if string is filled up to sn (useful for prefixLength)
        content += line.substr(0, line.size() - (charactersRead - _sn) - 1);
        break;
      } else {
        content += line;
      }
    }
  }
  streamInfile.close();
  if (content.size() != 0) {
    content += sequenceSeparator;
    charactersRead++;
    if (charactersRead < _sn - 1) {
      _sn = charactersRead;
    }
    D++;
    int64_t i = 0;
    int32_t leftB = 0;
    int32_t rightB = _n - 1;
    bool isSmallerThanMatch;
    unsigned char mismatchingSymbol;
    uint64_t prevPos = -2;
    uint32_t pos = _n - 1, len = 0;
    uint32_t iCurrentDoc = 0;
    while (i < content.size()) {
      if (content[i] == sequenceSeparator) {
        leftB = 0;
        rightB = _n - 1;
        len = 0;
        pos = _n - 1;
        phrasesVector.push_back(
            MatchInVectorBigger(iCurrentDoc, pos, len, 0, headNumber));
        headNumber++;
        bucketsForExpandedBWT[pos]--;
        if (maxValue < iCurrentDoc)
          maxValue = iCurrentDoc;
        iCurrentDoc = 0;
        ndoc++;
        if (i == 0) {
          listOfChars.push_back(sequenceSeparator);
        } else {
          listOfChars.push_back(content[i - 1]);
        }
      } else {
        computeMSFactorAt(content, i, &pos, &len, leftB, rightB,
                          isSmallerThanMatch, mismatchingSymbol);
        if (pos != prevPos + 1) {
          phrasesVector.push_back(MatchInVectorBigger(
              iCurrentDoc, pos, len, isSmallerThanMatch, headNumber));
          headNumber++;
          if (i == 0)
            listOfChars.push_back(sequenceSeparator);
          else
            listOfChars.push_back(content[i - 1]);
          if (bucketsForExpandedBWT[pos] > 0)
            bucketsForExpandedBWT[pos] = -bucketsForExpandedBWT[pos] - 1;
          else
            bucketsForExpandedBWT[pos]--;
        } else {
          if (bucketsForExpandedBWT[pos] >= 0)
            bucketsForExpandedBWT[pos]++;
          else
            bucketsForExpandedBWT[pos]--;
        }
        iCurrentDoc++;
        len--;

        if (leftB == rightB) {
          while (len > _PLCP[pos + 1]) {
            i++;
            iCurrentDoc++;
            len--;
            pos++;
            if (bucketsForExpandedBWT[pos] >= 0)
              bucketsForExpandedBWT[pos]++;
            else
              bucketsForExpandedBWT[pos]--;
          }
          std::pair<int, int> interval =
              adjustInterval(_ISA[pos + 1], _ISA[pos + 1], len);
          leftB = interval.first;
          rightB = interval.second;
        } else {
          std::pair<int, int> interval = contractLeft(leftB, rightB, len);
          leftB = interval.first;
          rightB = interval.second;
        }
      }
      i++;
      prevPos = pos;
    }
    std::string().swap(content);
  }
  std::cerr << "Finished parsing file of length: " << _sn << "\n";
  delete[] _LCP;
  delete[] _PLCP;
  delete _rmq;
  // for loop on phrases that substitutes phrases[i].start with _ISA[successor
  // of phrases[i]]
  uint64_t j = 0;
  for (uint64_t i = 0; i < phrasesVector.size() - 1; i++) {
    while (phrasesVector[j].start + phrasesVector[j].len <=
               phrasesVector[i].start + phrasesVector[i].len &
           phrasesVector[j].len != 0)
      j++;
    phrasesVector[i].toNext =
        phrasesVector[i].len > 0
            ? phrasesVector[i + 1].start - phrasesVector[i].start - 1
            : 0;
    phrasesVector[i].start =
        _ISA[phrasesVector[j].pos +
             (phrasesVector[i].start + phrasesVector[i].len -
              phrasesVector[j].start)];
    nextHead.push_back(j - i);
    if (phrasesVector[i].len == 0) {
      j++;
    }
  }
  nextHead.push_back(0);
  phrasesVector[phrasesVector.size() - 1].start = 0;

  std::sort(
      phrasesVector.begin(), phrasesVector.end(),
      [](const MatchInVectorBigger &headA, const MatchInVectorBigger &headB) {
        return (headA.pos < headB.pos) * (headA.pos != headB.pos) +
               (headA.idx < headB.idx) * (headA.pos == headB.pos);
      });
  for (uint32_t i = 0; i < phrasesVector.size(); i++) {
    auto M = MatchInSet(phrasesVector[i].len, phrasesVector[i].smaller,
                        phrasesVector[i].start);
    auto IM = ItemMatchInSet(phrasesVector[i].toNext, phrasesVector[i].idx);
    auto inserted = phrasesSet[phrasesVector[i].pos].insert(
        std::pair<MatchInSet, ItemMatchInSet>{M, IM});
    if (!inserted.second) {
      inserted.first->second.addIdx(phrasesVector[i].idx);
    }
  }
  std::vector<MatchInVectorBigger>().swap(phrasesVector);
  listOfChars.shrink_to_fit();
  std::cerr << "headNumber: " << headNumber << "\n";

  // count number of keys
  uint64_t uniqueHeadNumber = 0;
  for (uint32_t i = 0; i < _n; i++) {
    uniqueHeadNumber += phrasesSet[i].size();
  }
  std::cerr << "uniqueHeadNumber: " << uniqueHeadNumber << "\n";

  std::cerr << "ndoc: " << ndoc << "\n";
  std::cerr << "docBoundaries.size(): " << D << "\n";

  auto t2 = std::chrono::high_resolution_clock::now();
  uint64_t lzFactorizeTime =
      std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
  std::cerr << "Time to compute matching statistics: " << lzFactorizeTime
            << " milliseconds\n";

  std::cerr << "Going to compute ranks for positions\n";
  auto tRankStart = std::chrono::high_resolution_clock::now();
  // std::sort(setOfKeys.begin(), setOfKeys.end());
  int32_t rank = 1;
  int32_t *rankToHead = new int32_t[headNumber + 1]();
  int32_t *headToRank = new int32_t[headNumber + 1 + 6000];
  for (uint32_t i = 0; i < _n; i++) {
    uint32_t rankWithinMap = 0;
    for (std::map<MatchInSet, ItemMatchInSet>::iterator p =
             phrasesSet[_SA[i]].begin();
         p != phrasesSet[_SA[i]].end(); ++p) {
      for (auto position : p->second.idxs) {
        rankToHead[position] = rank;
        if (i == 0)
          rank++;
      }
      p->second.changeRank(rankWithinMap++);
      rank++;
    }
  }

  rankToHead[headNumber] = 0;

  auto libsaisStart = std::chrono::high_resolution_clock::now();
  if (int32_t err = libsais_int(rankToHead, headToRank, headNumber + 1, rank,
                                6000) != 0) {
    std::cerr << "libsais_int failed with error " << err << "\n";
    exit(0);
  }
  auto libsaisEnd = std::chrono::high_resolution_clock::now();
  std::cerr << "libsais_int ran in "
            << std::chrono::duration_cast<std::chrono::milliseconds>(
                   libsaisEnd - libsaisStart)
                   .count()
            << " milliseconds\n";

  // make ISA of heads in rankToHead from headToRank
  uint8_t *BWTheads = new uint8_t[headNumber];
  for (uint32_t i = 0; i < headNumber; i++) {
    rankToHead[headToRank[i + 1]] = i;
    BWTheads[i] = listOfChars[headToRank[i + 1]];
  }
  std::vector<uint8_t>().swap(listOfChars);
  delete[] headToRank;
  std::vector<uint8_t>().swap(listOfChars);
  std::cerr << "First rankToHead: " << rankToHead[0] << "\n";
  std::cerr << "Last rankToHead: " << rankToHead[headNumber - 1] << "\n";

  // assign rank of successive head to each idx of each phrase
  for (uint32_t i = 0; i < _n; i++) {
    for (std::map<MatchInSet, ItemMatchInSet>::iterator p =
             phrasesSet[i].begin();
         p != phrasesSet[i].end(); ++p) {
      for (uint32_t position = 0; position < p->second.idxs.size();
           position++) {
        // need to add offset to position, because we need to know the rank of
        // the idxs of the ''next'' phrase
        p->second.idxs[position] =
            rankToHead[p->second.idxs[position] +
                       nextHead[p->second.idxs[position]]];
      }
      std::sort(p->second.idxs.begin(), p->second.idxs.end());
    }
  }
  std::vector<uint16_t>().swap(nextHead);
  delete[] rankToHead;
  auto tRankEnd = std::chrono::high_resolution_clock::now();
  std::cerr << "Done computing ranks for positions in "
            << std::chrono::duration_cast<std::chrono::milliseconds>(tRankEnd -
                                                                     tRankStart)
                   .count()
            << " milliseconds\n";

  std::vector<std::vector<uint64_t>> prefixSumForPositions;
  prefixSumForPositions.resize(_n);
  uint64_t currentSum = 0;
  for (uint32_t i = 0; i < _n; i++) {
    for (auto p : phrasesSet[i]) {
      prefixSumForPositions[i].push_back(currentSum);
      currentSum += p.second.idxs.size();
    }
    prefixSumForPositions[i].push_back(currentSum);
  }
  std::cerr << "currentSum: " << currentSum << "\n";

  std::cerr << "Going to compute counterSmallerThanHead for positions\n";
  auto tcounterSmallerThanHeadStart = std::chrono::high_resolution_clock::now();
  uint32_t suffixesInBuffer = 0;
  uint64_t capOfBufferSuffixes;
  double RAMavailable =
      _sn < arg.buffer*1073741824 ? _sn : arg.buffer*1073741824;
  capOfBufferSuffixes =
      RAMavailable /
          (sizeof(MatchInSet) +
           sizeof(std::map<MatchInSet, ItemMatchInSet>::iterator)) +
      1;
  std::vector<std::vector<std::pair<
      MatchInSet, std::map<MatchInSet, ItemMatchInSet>::iterator>>>
      bufferSuffixes;
  bufferSuffixes.resize(_n);
  for (uint32_t i = 0; i < _n; i++) {
    bufferSuffixes[i].reserve(capOfBufferSuffixes);
  }
  std::cerr << "capOfBufferSuffixes = " << capOfBufferSuffixes << "\n";

  uint64_t counterBad = 0;
  uint64_t counterGood = 0;
  uint64_t counterDoNothing = 0;
  uint64_t *counterSmallerThanHead = new uint64_t[headNumber + 1]();
  for (uint32_t i = 0; i < _n; i++) {
    for (std::map<MatchInSet, ItemMatchInSet>::iterator p =
             phrasesSet[i].begin();
         p != phrasesSet[i].end(); ++p) {
      for (uint32_t idx = 0; idx < p->second.untilNext; idx++) {
        if (bucketsForExpandedBWT[i + 1 + idx] < 0) { // we have heads in the bucket to compare with
          bufferSuffixes[i + 1 + idx].push_back(
            std::pair<MatchInSet, std::map<MatchInSet, ItemMatchInSet>::iterator>{
                          MatchInSet(p->first.len - 1 - idx, p->first.smaller,
                          p->first.isaNext),
                          p
            });
          suffixesInBuffer++;
          if (suffixesInBuffer == capOfBufferSuffixes) {
            for (uint32_t b = 0; b < _n; b++) {
              for (uint32_t s = 0; s < bufferSuffixes[b].size(); s++) {
                auto pointer =
                    phrasesSet[b].lower_bound(bufferSuffixes[b][s].first);
                if (pointer == phrasesSet[b].end())
                  continue;
                if (pointer->first == bufferSuffixes[b][s].first) { // the head we found has the same length and
                                                                    // the same isaNext as our suffix
                                                                    // we have to compare each rank of the indices of toFind
                                                                    // (p.second) with the rank of the indices of pointer->second
                  counterBad++;
                  if (bufferSuffixes[b][s].second->second.idxs[bufferSuffixes[b][s].second->second.idxs.size() - 1] <
                      pointer->second.idxs[0]) { // every rank of the indices of toFind is
                                                 // smaller than the rank of the indices of
                                                 // pointer->second
                    counterSmallerThanHead
                        [prefixSumForPositions[b][pointer->second.rank]] +=
                        bufferSuffixes[b][s].second->second.idxs.size();
                    counterBad--;
                    counterGood++;
                    continue;
                  }
                  if (bufferSuffixes[b][s].second->second.idxs[0] >
                      pointer->second.idxs[pointer->second.idxs.size() - 1]) { // every rank of the indices of toFind is
                                                                               // bigger than the rank of the indices of
                                                                               // pointer->second
                    if (std::next(pointer) != phrasesSet[b].end())
                      counterSmallerThanHead
                          [prefixSumForPositions[b]
                                                [pointer->second.rank + 1]] +=
                          bufferSuffixes[b][s].second->second.idxs.size();
                    counterBad--;
                    counterGood++;
                    continue;
                  }
                  uint32_t indexForPointer = 0, indexForToFind = 0;
                  for (; indexForToFind <
                             bufferSuffixes[b][s].second->second.idxs.size() &&
                         indexForPointer < pointer->second.idxs.size();) {
                    // if the rank of the idx of toFind is smaller than the rank
                    // of the idx of pointer->second, increment
                    // counterSmallerThanHead
                    if (bufferSuffixes[b][s]
                            .second->second.idxs[indexForToFind] <
                        pointer->second.idxs[indexForPointer]) {
                      counterSmallerThanHead
                          [prefixSumForPositions[b][pointer->second.rank] +
                           indexForPointer]++;
                      indexForToFind++;
                    } else {
                      indexForPointer++;
                    }
                  }
                  if (indexForToFind <
                          bufferSuffixes[b][s].second->second.idxs.size() &&
                      std::next(pointer) != phrasesSet[b].end()) {
                    counterSmallerThanHead
                        [prefixSumForPositions[b][pointer->second.rank + 1]] +=
                        bufferSuffixes[b][s].second->second.idxs.size() -
                        indexForToFind;
                  }
                } else {
                  // easy case, all indices of toFind are smaller than the
                  // indices of pointer->second
                  counterGood++;
                  counterSmallerThanHead
                      [prefixSumForPositions[b][pointer->second.rank]] +=
                      bufferSuffixes[b][s].second->second.idxs.size();
                }
              }
            }
            // TODO: better free memory, this is ugly because iterators seems
            // not to be released with vector.clear()
            for (uint32_t i = 0; i < _n; i++) {
              bufferSuffixes[i] = std::vector<
                  std::pair<MatchInSet, std::map<MatchInSet, ItemMatchInSet>::iterator>>();
              bufferSuffixes[i].reserve(capOfBufferSuffixes);
            }
            suffixesInBuffer = 0;
          }
        } else {
          counterDoNothing++;
        }
      }
    }
  }
  if (suffixesInBuffer != 0) {
    for (uint32_t b = 0; b < _n; b++) {
      for (uint32_t s = 0; s < bufferSuffixes[b].size(); s++) {
        auto pointer = phrasesSet[b].lower_bound(bufferSuffixes[b][s].first);
        if (pointer == phrasesSet[b].end())
          continue;
        if (pointer->first ==
            bufferSuffixes[b][s].first) { // the head we found has the same length and the same
                                          // isaNext as our suffix
                                          // we have to compare each rank of the indices of toFind (p.second)
                                          // with the rank of the indices of pointer->second  
          counterBad++;
          if (bufferSuffixes[b][s].second->second.idxs[bufferSuffixes[b][s].second->second.idxs.size() - 1] <
              pointer->second.idxs[0]) { // every rank of the indices of toFind is smaller
                                         // than the rank of the indices of pointer->second
            counterSmallerThanHead
                [prefixSumForPositions[b][pointer->second.rank]] +=
                bufferSuffixes[b][s].second->second.idxs.size();
            counterBad--;
            counterGood++;
            continue;
          }
          if (bufferSuffixes[b][s].second->second.idxs[0] >
              pointer->second.idxs[pointer->second.idxs.size() - 1]) { // every rank of the indices of toFind is bigger
                                                                       // than the rank of the indices of pointer->second
            if (std::next(pointer) != phrasesSet[b].end())
              counterSmallerThanHead
                  [prefixSumForPositions[b][pointer->second.rank + 1]] +=
                  bufferSuffixes[b][s].second->second.idxs.size();
            counterBad--;
            counterGood++;
            continue;
          }
          uint32_t indexForPointer = 0, indexForToFind = 0;
          for (; indexForToFind <
                     bufferSuffixes[b][s].second->second.idxs.size() &&
                 indexForPointer < pointer->second.idxs.size();) {
            // if the rank of the idx of toFind is smaller than the rank of the
            // idx of pointer->second, increment counterSmallerThanHead
            if (bufferSuffixes[b][s].second->second.idxs[indexForToFind] <
                pointer->second.idxs[indexForPointer]) {
              counterSmallerThanHead
                  [prefixSumForPositions[b][pointer->second.rank] +
                   indexForPointer]++;
              indexForToFind++;
            } else {
              indexForPointer++;
            }
          }
          if (indexForToFind <
                  bufferSuffixes[b][s].second->second.idxs.size() &&
              std::next(pointer) != phrasesSet[b].end()) {
            // deal with the remaining indices of toFind
            counterSmallerThanHead
                [prefixSumForPositions[b][pointer->second.rank + 1]] +=
                bufferSuffixes[b][s].second->second.idxs.size() -
                indexForToFind;
          }
        } else {
          // easy case, all indices of toFind are smaller than the indices of
          // pointer->second
          counterGood++;
          counterSmallerThanHead[prefixSumForPositions[b]
                                                      [pointer->second.rank]] +=
              bufferSuffixes[b][s].second->second.idxs.size();
        }
      }
    }
    suffixesInBuffer = 0;
  }

  std::vector<std::vector<std::pair<
      MatchInSet, std::map<MatchInSet, ItemMatchInSet>::iterator>>>()
      .swap(bufferSuffixes);
  auto tcounterSmallerThanHeadEnd = std::chrono::high_resolution_clock::now();
  std::cerr << "counterBad: " << counterBad << "\n";
  std::cerr << "counterGood: " << counterGood << "\n";
  std::cerr << "counterDoNothing: " << counterDoNothing << "\n";
  
  std::vector<std::map<MatchInSet, ItemMatchInSet>>().swap(phrasesSet);
  std::cerr << "Done computing counterSmallerThanHead for positions in "
            << std::chrono::duration_cast<std::chrono::milliseconds>(
                   tcounterSmallerThanHeadEnd - tcounterSmallerThanHeadStart)
                   .count()
            << " milliseconds\n";

  // dump to file the counterSmallerThanHead
  std::ofstream streamOutfile(
      arg.outname + ".counterSmallerThanHead_true", std::ios::out | std::ios::binary);
  streamOutfile.write((char *)&counterSmallerThanHead[0],
                      sizeof(uint64_t) * (headNumber + 1));
  streamOutfile.close();

  // interleave counterSmallerThanHead with BWTHeads
  int64_t *bucketsForExpandedBWT_copy = new int64_t[_n]();
  for (uint32_t i = 0; i < _n; i++) {
    bucketsForExpandedBWT_copy[i] = bucketsForExpandedBWT[i];
  }
  // invert data in bucketsForExpandedBWT w.r.t. _ISA
  for (uint32_t i = 0; i < _n; i++) {
    bucketsForExpandedBWT[_ISA[i]] = bucketsForExpandedBWT_copy[i];
  }
  std::cerr << "Inverted data in bucketsForExpandedBWT\n";
  delete[] bucketsForExpandedBWT_copy;

  bool RLEWrite = arg.format;
  if (!RLEWrite) {
    std::ofstream streamOutfile(arg.outname + ".bwt",
                                std::ios::out | std::ios::binary);
    std::vector<uint8_t> bufferWrite;
    bufferWrite.reserve(1024 * 1024);

    // write BWT_collection to file
    streamOutfile.write((char *)&BWTheads[0], sizeof(uint8_t) * (D - 1));
    uint32_t headCounter = D - 1;
    for (uint32_t i = 1; i < _n; i++) {
      uint8_t characterEqualToReference = _BWT[i];
      if (bucketsForExpandedBWT[i] >= 0) {
        for (uint64_t counter = 0; counter < bucketsForExpandedBWT[i];
             counter++) {
          bufferWrite.push_back(characterEqualToReference);
          if (bufferWrite.size() == bufferWrite.capacity()) {
            streamOutfile.write((char *)&bufferWrite[0],
                                sizeof(uint8_t) * bufferWrite.size());
            bufferWrite.clear();
          }
        }
      } else {
        for (uint64_t subBucket = 0;
             subBucket < prefixSumForPositions[_SA[i]].size() - 1;
             subBucket++) { // -1 because we added the end of the last subBucket
          for (uint64_t counter = prefixSumForPositions[_SA[i]][subBucket];
               counter < prefixSumForPositions[_SA[i]][subBucket + 1];
               counter++) {
            for (uint64_t counter2 = 0;
                 counter2 < counterSmallerThanHead[counter]; counter2++) {
              bufferWrite.push_back(characterEqualToReference);
              if (bufferWrite.size() == bufferWrite.capacity()) {
                streamOutfile.write((char *)&bufferWrite[0],
                                    sizeof(uint8_t) * bufferWrite.size());
                bufferWrite.clear();
              }
              bucketsForExpandedBWT[i]++;
            }
            bufferWrite.push_back(BWTheads[headCounter++]);
            if (bufferWrite.size() == bufferWrite.capacity()) {
              streamOutfile.write((char *)&bufferWrite[0],
                                  sizeof(uint8_t) * bufferWrite.size());
              bufferWrite.clear();
            }
            bucketsForExpandedBWT[i]++;
          }
        }
        for (int64_t counter = bucketsForExpandedBWT[i]; counter < 0;
             counter++) {
          bufferWrite.push_back(characterEqualToReference);
          if (bufferWrite.size() == bufferWrite.capacity()) {
            streamOutfile.write((char *)&bufferWrite[0],
                                sizeof(uint8_t) * bufferWrite.size());
            bufferWrite.clear();
          }
        }
      }
    }
    if (bufferWrite.size() > 0) {
      streamOutfile.write((char *)&bufferWrite[0],
                          sizeof(uint8_t) * bufferWrite.size());
      bufferWrite.clear();
    }
    streamOutfile.close();
  } else {
    uint8_t prevChar = (char)0;
    uint64_t runLength = 0;

    std::ofstream streamOutfile(arg.outname + ".rl_bwt",
                                std::ios::out | std::ios::binary);
    std::vector<uint8_t> bufferWrite;
    bufferWrite.reserve(1024 * 1024);

    // write BWT_collection to file
    for (uint64_t d = 0; d < D - 1; d++) {
      if (prevChar != BWTheads[d]) {
        if (runLength > 0) {
          streamOutfile.write((char *)&runLength, sizeof(uint64_t));
          streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
          runLength = 1;
          prevChar = BWTheads[d];
        } else {
          runLength = 1;
          prevChar = BWTheads[d];
        }
      } else {
        runLength++;
      }
    }
    uint64_t headCounter = D - 1;
    for (uint32_t i = 1; i < _x.size(); i++) {
      uint8_t characterEqualToReference = _BWT[i];
      if (bucketsForExpandedBWT[i] > 0) {
        if (prevChar != characterEqualToReference) {
          streamOutfile.write((char *)&runLength, sizeof(uint64_t));
          streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
          runLength = bucketsForExpandedBWT[i];
          prevChar = characterEqualToReference;
        } else {
          runLength += bucketsForExpandedBWT[i];
        }
      } else if (bucketsForExpandedBWT[i] < 0) {
        for (uint64_t subBucket = 0;
             subBucket < prefixSumForPositions[_SA[i]].size() - 1;
             subBucket++) { // -1 because we added the end of the last subBucket
          for (uint64_t counter = prefixSumForPositions[_SA[i]][subBucket];
               counter < prefixSumForPositions[_SA[i]][subBucket + 1];
               counter++) {
            if (counterSmallerThanHead[counter]) {
              if (prevChar != characterEqualToReference) {
                streamOutfile.write((char *)&runLength, sizeof(uint64_t));
                streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
                runLength = counterSmallerThanHead[counter];
                prevChar = characterEqualToReference;
              } else {
                runLength += counterSmallerThanHead[counter];
              }
              bucketsForExpandedBWT[i] += counterSmallerThanHead[counter];
            }
            auto x = BWTheads[headCounter++];
            if (x != prevChar) {
              streamOutfile.write((char *)&runLength, sizeof(uint64_t));
              streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
              runLength = 1;
              prevChar = x;
            } else {
              runLength++;
            }
            bucketsForExpandedBWT[i]++;
          }
          if (bucketsForExpandedBWT[i] != 0) {
            if (prevChar != characterEqualToReference) {
              streamOutfile.write((char *)&runLength, sizeof(uint64_t));
              streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
              runLength = -bucketsForExpandedBWT[i];
              prevChar = characterEqualToReference;
            } else {
              runLength += -bucketsForExpandedBWT[i];
            }
          }
        }
      }
    }
    streamOutfile.write((char *)&runLength, sizeof(uint64_t));
    streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
    streamOutfile.close();
  }
  delete[] BWTheads;
  std::vector<std::vector<uint64_t>>().swap(prefixSumForPositions);
  delete[] bucketsForExpandedBWT;
  delete[] counterSmallerThanHead;

}

void process_collection_large_reference(Args arg, std::string &collFileName) {
  std::cerr << "File is in memory\n";
  std::cerr << "_x.len: " << _n << '\n';
  std::cerr << "_sx.len: " << _sn << '\n';
  auto t1 = std::chrono::high_resolution_clock::now();

  unsigned int numfactors = 0;

  unsigned int inc = 100000000;
  uint64_t mark = inc;

  std::cerr << "About to start main parsing loop...\n";

  uint32_t ndoc = 1;
  int64_t *bucketsForExpandedBWT = new int64_t[_n]();
  bucketsForExpandedBWT[_n - 1] = 0;

  uint64_t i = 0;

  uint64_t maxValue = 0;
  std::vector<uint8_t> listOfChars;

  std::ifstream streamInfile(collFileName, std::ios::in);
  std::string line, content;
  content.reserve(_n * 2);
  uint64_t charactersRead = 0;
  uint32_t headNumber = 0;

  std::unordered_map<uint32_t, std::map<MatchInSet, ItemMatchInSet>> phrasesSet;
  phrasesSet.reserve(2000000);
  phrasesSet[_n - 1] = std::map<MatchInSet, ItemMatchInSet>();
  std::vector<uint32_t> setOfKeys;
  setOfKeys.reserve(2000000);
  setOfKeys.push_back(_n - 1);
  std::vector<uint16_t> nextHead;
  nextHead.reserve(2000000);

  uint64_t capPhrasesVector = 1000000000 / sizeof(MatchInVectorBigger);
  std::vector<MatchInVectorBigger> phrasesVector;

  // open buffer to file to which save phrasesVector in reverse order
  std::ofstream streamOutfile(arg.outname + ".phrases",
                              std::ios::out | std::ios::binary);

  while (std::getline(streamInfile, line).good()) {
    if (line.empty() || line[0] == '>') {
      content += sequenceSeparator;
      charactersRead++;
      int64_t i = 0;
      int32_t leftB = 0;
      int32_t rightB = _n - 1;
      bool isSmallerThanMatch;
      unsigned char mismatchingSymbol;
      uint64_t prevPos = -2;
      uint32_t pos = _n - 1, len = 0;
      uint32_t iCurrentDoc = 0;
      D++;
      while (i < ((int64_t)content.size()) - 1) {
        computeMSFactorAt(content, i, &pos, &len, leftB, rightB,
                          isSmallerThanMatch, mismatchingSymbol);
        if (pos != prevPos + 1) {
          phrasesVector.push_back(MatchInVectorBigger(
              iCurrentDoc, pos, len, isSmallerThanMatch, headNumber));
          headNumber++;
          if (i == 0)
            listOfChars.push_back(sequenceSeparator);
          else
            listOfChars.push_back(content[i - 1]);
          if (bucketsForExpandedBWT[pos] > 0)
            bucketsForExpandedBWT[pos] = -bucketsForExpandedBWT[pos] - 1;
          else
            bucketsForExpandedBWT[pos]--;
        } else {
          if (bucketsForExpandedBWT[pos] >= 0)
            bucketsForExpandedBWT[pos]++;
          else
            bucketsForExpandedBWT[pos]--;
        }
        iCurrentDoc++;
        len--;

        if (leftB == rightB) {
          while (len > _PLCP[pos + 1]) {
            i++;
            iCurrentDoc++;
            len--;
            pos++;
            if (bucketsForExpandedBWT[pos] >= 0)
              bucketsForExpandedBWT[pos]++;
            else
              bucketsForExpandedBWT[pos]--;
          }
          std::pair<int, int> interval =
              adjustInterval(_ISA[pos + 1], _ISA[pos + 1], len);
          leftB = interval.first;
          rightB = interval.second;
        } else {
          std::pair<int, int> interval = contractLeft(leftB, rightB, len);
          leftB = interval.first;
          rightB = interval.second;
        }
        i++;
        prevPos = pos;
      }
      len = 0;
      pos = _n - 1;
      phrasesVector.push_back(
          MatchInVectorBigger(iCurrentDoc, pos, len, 0, headNumber));
      headNumber++;
      bucketsForExpandedBWT[pos]--;
      if (maxValue < iCurrentDoc)
        maxValue = iCurrentDoc;
      iCurrentDoc = 0;
      ndoc++;
      if (i == 0) {
        listOfChars.push_back(sequenceSeparator);
      } else {
        listOfChars.push_back(content[content.size() - 2]);
      }
      content.erase();
      if (phrasesVector.size() >= capPhrasesVector) {
        uint32_t j = 0;
        for (uint32_t i = 0; i < phrasesVector.size() - 1; i++) {
          if (phrasesSet
                  .try_emplace(phrasesVector[i].pos,
                               std::map<MatchInSet, ItemMatchInSet>())
                  .second) {
            setOfKeys.push_back(phrasesVector[i].pos);
          }
          while (phrasesVector[j].start + phrasesVector[j].len <=
                     phrasesVector[i].start + phrasesVector[i].len &
                 phrasesVector[j].len != 0)
            j++;
          phrasesVector[i].toNext =
              phrasesVector[i].len > 0
                  ? phrasesVector[i + 1].start - phrasesVector[i].start - 1
                  : 0;
          // get ISA next phrase
          phrasesVector[i].start =
              _ISA[phrasesVector[j].pos +
                   (phrasesVector[i].start + phrasesVector[i].len -
                    phrasesVector[j].start)];
          nextHead.push_back(j - i);
          if (phrasesVector[i].len == 0) {
            j++;
          }
        }
        nextHead.push_back(0);
        phrasesVector[phrasesVector.size() - 1].start = 0;

        std::sort(phrasesVector.begin(), phrasesVector.end(),
                  [](const MatchInVectorBigger &headA,
                     const MatchInVectorBigger &headB) {
                    return (headA.pos < headB.pos) * (headA.pos != headB.pos) +
                           (headA.idx < headB.idx) * (headA.pos == headB.pos);
                  });

        // write phrasesVector to file
        streamOutfile.write((char *)&phrasesVector[0],
                            sizeof(MatchInVectorBigger) * phrasesVector.size());

        phrasesVector.clear();
      }
    } else if (!line.empty()) {
      charactersRead += line.size();
      if (charactersRead >=
          _sn - 1) { // if string is filled up to sn (useful for prefixLength)
        content += line.substr(0, line.size() - (charactersRead - _sn) - 1);
        break;
      } else {
        content += line;
      }
    }
  }
  streamInfile.close();
  if (content.size() != 0) {
    content += sequenceSeparator;
    charactersRead++;
    if (charactersRead < _sn - 1) {
      _sn = charactersRead;
    }
    D++;
    int64_t i = 0;
    int32_t leftB = 0;
    int32_t rightB = _n - 1;
    bool isSmallerThanMatch;
    unsigned char mismatchingSymbol;
    uint64_t prevPos = -2;
    uint32_t pos = _n - 1, len = 0;
    uint32_t iCurrentDoc = 0;
    while (i < content.size()) {
      if (content[i] == sequenceSeparator) {
        leftB = 0;
        rightB = _n - 1;
        len = 0;
        pos = _n - 1;
        phrasesVector.push_back(
            MatchInVectorBigger(iCurrentDoc, pos, len, 0, headNumber));
        headNumber++;
        bucketsForExpandedBWT[pos]--;
        if (maxValue < iCurrentDoc)
          maxValue = iCurrentDoc;
        iCurrentDoc = 0;
        ndoc++;
        if (i == 0) {
          listOfChars.push_back(sequenceSeparator);
        } else {
          listOfChars.push_back(content[i - 1]);
        }
      } else {
        computeMSFactorAt(content, i, &pos, &len, leftB, rightB,
                          isSmallerThanMatch, mismatchingSymbol);
        if (pos != prevPos + 1) {
          phrasesVector.push_back(MatchInVectorBigger(
              iCurrentDoc, pos, len, isSmallerThanMatch, headNumber));
          headNumber++;
          if (i == 0)
            listOfChars.push_back(sequenceSeparator);
          else
            listOfChars.push_back(content[i - 1]);
          if (bucketsForExpandedBWT[pos] > 0)
            bucketsForExpandedBWT[pos] = -bucketsForExpandedBWT[pos] - 1;
          else
            bucketsForExpandedBWT[pos]--;
        } else {
          if (bucketsForExpandedBWT[pos] >= 0)
            bucketsForExpandedBWT[pos]++;
          else
            bucketsForExpandedBWT[pos]--;
        }
        iCurrentDoc++;
        len--;

        if (leftB == rightB) {
          while (len > _PLCP[pos + 1]) {
            i++;
            iCurrentDoc++;
            len--;
            pos++;
            if (bucketsForExpandedBWT[pos] >= 0)
              bucketsForExpandedBWT[pos]++;
            else
              bucketsForExpandedBWT[pos]--;
          }
          std::pair<int, int> interval =
              adjustInterval(_ISA[pos + 1], _ISA[pos + 1], len);
          leftB = interval.first;
          rightB = interval.second;
        } else {
          std::pair<int, int> interval = contractLeft(leftB, rightB, len);
          leftB = interval.first;
          rightB = interval.second;
        }
      }
      i++;
      prevPos = pos;
    }
    std::string().swap(content);
  }
  std::cerr << "Finished parsing file of length: " << _sn << "\n";
  delete[] _LCP;
  delete[] _PLCP;
  delete _rmq;
  // for loop on phrases that substitutes phrases[i].start with _ISA[successor
  // of phrases[i]]
  uint64_t j = 0;
  for (uint64_t i = 0; i < phrasesVector.size() - 1; i++) {
    if (phrasesSet
            .try_emplace(phrasesVector[i].pos,
                         std::map<MatchInSet, ItemMatchInSet>())
            .second) {
      setOfKeys.push_back(phrasesVector[i].pos);
    }
    while (phrasesVector[j].start + phrasesVector[j].len <=
               phrasesVector[i].start + phrasesVector[i].len &
           phrasesVector[j].len != 0)
      j++;
    phrasesVector[i].toNext =
        phrasesVector[i].len > 0
            ? phrasesVector[i + 1].start - phrasesVector[i].start - 1
            : 0;
    phrasesVector[i].start =
        _ISA[phrasesVector[j].pos +
             (phrasesVector[i].start + phrasesVector[i].len -
              phrasesVector[j].start)];
    nextHead.push_back(j - i);
    if (phrasesVector[i].len == 0) {
      j++;
    }
  }
  nextHead.push_back(0);
  phrasesVector[phrasesVector.size() - 1].start = 0;

  std::sort(
      phrasesVector.begin(), phrasesVector.end(),
      [](const MatchInVectorBigger &headA, const MatchInVectorBigger &headB) {
        return (headA.pos < headB.pos) * (headA.pos != headB.pos) +
               (headA.idx < headB.idx) * (headA.pos == headB.pos);
      });

  // write phrasesVector to file
  streamOutfile.write((char *)&phrasesVector[0],
                      sizeof(MatchInVectorBigger) * phrasesVector.size());
  streamOutfile.close();

  std::vector<MatchInVectorBigger>().swap(phrasesVector);

  std::ifstream streamInfilePhrases(arg.outname + ".phrases",
                                    std::ios::in | std::ios::binary);
  MatchInVectorBigger currentPhrase;
  while (streamInfilePhrases.read((char *)&currentPhrase,
                                  sizeof(MatchInVectorBigger))) {
    auto M = MatchInSet(currentPhrase.len, currentPhrase.smaller,
                        currentPhrase.start);
    auto IM = ItemMatchInSet(currentPhrase.toNext, currentPhrase.idx);
    auto inserted = phrasesSet[currentPhrase.pos].insert(
        std::pair<MatchInSet, ItemMatchInSet>{M, IM});
    if (!inserted.second) {
      inserted.first->second.addIdx(currentPhrase.idx);
    }
  }
  streamInfilePhrases.close();
  std::remove((arg.outname + ".phrases").c_str());
  std::cerr << "phrasesSet.size(): " << phrasesSet.size() << "\n";

  listOfChars.shrink_to_fit();
  std::cerr << "headNumber: " << headNumber << "\n";
  std::cerr << "ndoc: " << ndoc << "\n";
  std::cerr << "docBoundaries.size(): " << D << "\n";

  auto t2 = std::chrono::high_resolution_clock::now();
  uint64_t lzFactorizeTime =
      std::chrono::duration_cast<std::chrono::milliseconds>(t2 - t1).count();
  std::cerr << "Time to compute matching statistics: " << lzFactorizeTime
            << " milliseconds\n";

  std::cerr << "Going to compute ranks for positions\n";
  auto tRankStart = std::chrono::high_resolution_clock::now();
  std::sort(
      setOfKeys.begin(), setOfKeys.end(),
      [](const uint32_t &a, const uint32_t &b) { return _ISA[a] < _ISA[b]; });
  int32_t rank = 1;
  int32_t *rankToHead = new int32_t[headNumber + 1]();
  int32_t *headToRank = new int32_t[headNumber + 1 + 6000];
  for (auto i : setOfKeys) {
    uint32_t rankWithinMap = 0;
    for (std::map<MatchInSet, ItemMatchInSet>::iterator p =
             phrasesSet[i].begin();
         p != phrasesSet[i].end(); ++p) {
      for (auto position : p->second.idxs) {
        rankToHead[position] = rank;
        if (i == _n - 1)
          rank++;
      }
      p->second.changeRank(rankWithinMap++);
      rank++;
    }
  }
  std::cerr << "Rank: " << rank << "\n";
  rankToHead[headNumber] = 0;

  auto libsaisStart = std::chrono::high_resolution_clock::now();
  if (libsais_int(rankToHead, headToRank, headNumber + 1, rank, 6000) != 0) {
    std::cerr << "libsais_int failed\n";
    exit(0);
  }
  auto libsaisEnd = std::chrono::high_resolution_clock::now();
  std::cerr << "libsais_int ran in "
            << std::chrono::duration_cast<std::chrono::milliseconds>(
                   libsaisEnd - libsaisStart)
                   .count()
            << " milliseconds\n";

  // make ISA of heads in rankToHead from headToRank
  uint8_t *BWTheads = new uint8_t[headNumber + 1]();
  for (uint32_t i = 0; i < headNumber; i++) {
    rankToHead[headToRank[i + 1]] = i;
    BWTheads[i] = listOfChars[headToRank[i + 1]];
  }
  std::vector<uint8_t>().swap(listOfChars);
  delete[] headToRank;

  std::cerr << "First rankToHead: " << rankToHead[0] << "\n";
  std::cerr << "Last rankToHead: " << rankToHead[headNumber - 1] << "\n";

  // assign rank of successive head to each idx of each phrase
  for (auto i : setOfKeys) {
    for (std::map<MatchInSet, ItemMatchInSet>::iterator p =
             phrasesSet[i].begin();
         p != phrasesSet[i].end(); ++p) {
      for (uint32_t position = 0; position < p->second.idxs.size();
           position++) {
        // need to add offset to position, because we need to know the rank of
        // the idxs of the ''next'' phrase
        p->second.idxs[position] =
            rankToHead[p->second.idxs[position] +
                       nextHead[p->second.idxs[position]]];
      }
      std::sort(p->second.idxs.begin(), p->second.idxs.end());
    }
  }
  delete[] rankToHead;
  std::vector<uint16_t>().swap(nextHead);
  auto tRankEnd = std::chrono::high_resolution_clock::now();
  std::cerr << "Done computing ranks for positions in "
            << std::chrono::duration_cast<std::chrono::milliseconds>(tRankEnd -
                                                                     tRankStart)
                   .count()
            << " milliseconds\n";

  std::sort(setOfKeys.begin(), setOfKeys.end());
  std::unordered_map<uint32_t, std::vector<uint64_t>> prefixSumForPositions;
  uint64_t currentSum = 0;
  for (auto i : setOfKeys) {
    prefixSumForPositions[i] = std::vector<uint64_t>();
    for (auto p : phrasesSet[i]) {
      prefixSumForPositions[i].push_back(currentSum);
      currentSum += p.second.idxs.size();
    }
    prefixSumForPositions[i].push_back(currentSum);
  }
  std::cerr << "currentSum: " << currentSum << "\n";

  std::cerr << "Going to compute counterSmallerThanHead for positions\n";
  auto tcounterSmallerThanHeadStart = std::chrono::high_resolution_clock::now();
  
  uint64_t counterBad = 0;
  uint64_t counterGood = 0;
  uint64_t counterDoNothing = 0;
  uint64_t *counterSmallerThanHead = new uint64_t[headNumber + 1]();

  for (auto i : setOfKeys) {
    for (std::map<MatchInSet, ItemMatchInSet>::iterator p =
             phrasesSet[i].begin();
         p != phrasesSet[i].end(); ++p) {
      for (uint32_t idx = 0; idx < p->second.untilNext; idx++) {
        if (bucketsForExpandedBWT[i + 1 + idx] <
            0) { // we have heads in the bucket to compare with
          auto toFind = MatchInSet(p->first.len - 1 - idx, p->first.smaller,
                                   p->first.isaNext);
          auto pointer = phrasesSet[i + 1 + idx].lower_bound(toFind);
          if (pointer == phrasesSet[i + 1 + idx].end())
            continue;
          if (pointer->first == toFind) { // the head we found has the same length and the same
                                          // isaNext as our suffix
                                          // we have to compare each rank of the indices of toFind (p.second)
                                          // with the rank of the indices of pointer->second
            counterBad++;
            if (p->second.idxs[p->second.idxs.size() - 1] <
                pointer->second.idxs[0]) { // every rank of the indices of
                                           // toFind is smaller than the rank of
                                           // the indices of pointer->second
              counterSmallerThanHead
                  [prefixSumForPositions[i + 1 + idx][pointer->second.rank]] +=
                  p->second.idxs.size();
              counterBad--;
              counterGood++;
              continue;
            }
            if (p->second.idxs[0] >
                pointer->second.idxs[pointer->second.idxs.size() - 1]) { // every rank of the indices of
                                                                         // toFind is bigger than the rank of
                                                                         // the indices of pointer->second
              if (std::next(pointer) != phrasesSet[i + 1 + idx].end()) {
                counterSmallerThanHead
                    [prefixSumForPositions[i + 1 + idx]
                                          [pointer->second.rank + 1]] +=
                    p->second.idxs.size();
              }
              counterBad--;
              counterGood++;
              continue;
            }
            uint32_t indexForPointer = 0, indexForToFind = 0;
            for (indexForToFind;
                 indexForToFind < p->second.idxs.size() &&
                 indexForPointer < pointer->second.idxs.size();) {
              // if the rank of the idx of toFind is smaller than the rank of
              // the idx of pointer->second, increment counterSmallerThanHead
              if (p->second.idxs[indexForToFind] <
                  pointer->second.idxs[indexForPointer]) {
                counterSmallerThanHead
                    [prefixSumForPositions[i + 1 + idx][pointer->second.rank] +
                     indexForPointer]++;
                indexForToFind++;
              } else {
                indexForPointer++;
              }
            }
            if (indexForToFind < p->second.idxs.size() &&
                std::next(pointer) != phrasesSet[i + 1 + idx].end()) {
              counterSmallerThanHead
                  [prefixSumForPositions[i + 1 + idx]
                                        [pointer->second.rank + 1]] +=
                  p->second.idxs.size() - indexForToFind;
            }
          } else {
            // easy case, all indices of toFind are smaller than the indices of
            // pointer->second
            counterGood++;
            counterSmallerThanHead
                [prefixSumForPositions[i + 1 + idx][pointer->second.rank]] +=
                p->second.idxs.size();
          }
        } else {
          counterDoNothing++;
        }
      }
    }
  }

  auto tcounterSmallerThanHeadEnd = std::chrono::high_resolution_clock::now();
  std::cerr << "counterBad: " << counterBad << "\n";
  std::cerr << "counterGood: " << counterGood << "\n";
  std::cerr << "counterDoNothing: " << counterDoNothing << "\n";
  std::unordered_map<uint32_t, std::map<MatchInSet, ItemMatchInSet>>().swap(
      phrasesSet);
  std::cerr << "Done computing counterSmallerThanHead for positions in "
            << std::chrono::duration_cast<std::chrono::milliseconds>(
                   tcounterSmallerThanHeadEnd - tcounterSmallerThanHeadStart)
                   .count()
            << " milliseconds\n";

  // interleave counterSmallerThanHead with BWTHeads
  int64_t *bucketsForExpandedBWT_copy = new int64_t[_n];
  for (uint32_t i = 0; i < _n; i++) {
    bucketsForExpandedBWT_copy[i] = bucketsForExpandedBWT[i];
  }

  // invert data in bucketsForExpandedBWT w.r.t. _ISA
  for (uint32_t i = 0; i < _n; i++) {
    bucketsForExpandedBWT[_ISA[i]] = bucketsForExpandedBWT_copy[i];
  }
  std::cerr << "Inverted data in bucketsForExpandedBWT\n";
  delete[] bucketsForExpandedBWT_copy;

  bool RLEWrite = arg.format;
  if (!RLEWrite) {
    std::ofstream streamOutfile(arg.outname + ".bwt",
                                std::ios::out | std::ios::binary);
    std::vector<uint8_t> bufferWrite;
    bufferWrite.reserve(1024 * 1024);

    // write BWT_collection to file
    streamOutfile.write((char *)&BWTheads[0], sizeof(uint8_t) * (D - 1));
    uint32_t headCounter = D - 1;
    for (uint32_t i = 1; i < _n; i++) {
      uint8_t characterEqualToReference = _BWT[i];
      if (bucketsForExpandedBWT[i] >= 0) {
        for (uint64_t counter = 0; counter < bucketsForExpandedBWT[i];
             counter++) {
          bufferWrite.push_back(characterEqualToReference);
          if (bufferWrite.size() == bufferWrite.capacity()) {
            streamOutfile.write((char *)&bufferWrite[0],
                                sizeof(uint8_t) * bufferWrite.size());
            bufferWrite.clear();
          }
        }
      } else {
        for (uint64_t subBucket = 0;
             subBucket < prefixSumForPositions[_SA[i]].size() - 1;
             subBucket++) { // -1 because we added the end of the last subBucket
          for (uint64_t counter = prefixSumForPositions[_SA[i]][subBucket];
               counter < prefixSumForPositions[_SA[i]][subBucket + 1];
               counter++) {
            for (uint64_t counter2 = 0;
                 counter2 < counterSmallerThanHead[counter]; counter2++) {
              bufferWrite.push_back(characterEqualToReference);
              if (bufferWrite.size() == bufferWrite.capacity()) {
                streamOutfile.write((char *)&bufferWrite[0],
                                    sizeof(uint8_t) * bufferWrite.size());
                bufferWrite.clear();
              }
              bucketsForExpandedBWT[i]++;
            }
            bufferWrite.push_back(BWTheads[headCounter++]);
            if (bufferWrite.size() == bufferWrite.capacity()) {
              streamOutfile.write((char *)&bufferWrite[0],
                                  sizeof(uint8_t) * bufferWrite.size());
              bufferWrite.clear();
            }
            bucketsForExpandedBWT[i]++;
          }
        }
        for (int64_t counter = bucketsForExpandedBWT[i]; counter < 0;
             counter++) {
          bufferWrite.push_back(characterEqualToReference);
          if (bufferWrite.size() == bufferWrite.capacity()) {
            streamOutfile.write((char *)&bufferWrite[0],
                                sizeof(uint8_t) * bufferWrite.size());
            bufferWrite.clear();
          }
        }
      }
    }
    if (bufferWrite.size() > 0) {
      streamOutfile.write((char *)&bufferWrite[0],
                          sizeof(uint8_t) * bufferWrite.size());
      bufferWrite.clear();
    }
    streamOutfile.close();
  } else {
    uint8_t prevChar = (char)0;
    uint64_t runLength = 0;

    std::ofstream streamOutfile(arg.outname + ".rl_bwt",
                                std::ios::out | std::ios::binary);
    std::vector<uint8_t> bufferWrite;
    bufferWrite.reserve(1024 * 1024);

    // write BWT_collection to file
    for (uint64_t d = 0; d < D - 1; d++) {
      if (prevChar != BWTheads[d]) {
        if (runLength > 0) {
          streamOutfile.write((char *)&runLength, sizeof(uint64_t));
          streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
          runLength = 1;
          prevChar = BWTheads[d];
        } else {
          runLength = 1;
          prevChar = BWTheads[d];
        }
      } else {
        runLength++;
      }
    }
    uint64_t headCounter = D - 1;
    for (uint32_t i = 1; i < _x.size(); i++) {
      uint8_t characterEqualToReference = _BWT[i];
      if (bucketsForExpandedBWT[i] > 0) {
        if (prevChar != characterEqualToReference) {
          streamOutfile.write((char *)&runLength, sizeof(uint64_t));
          streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
          runLength = bucketsForExpandedBWT[i];
          prevChar = characterEqualToReference;
        } else {
          runLength += bucketsForExpandedBWT[i];
        }
      } else if (bucketsForExpandedBWT[i] < 0) {
        for (uint64_t subBucket = 0;
             subBucket < prefixSumForPositions[_SA[i]].size() - 1;
             subBucket++) { // -1 because we added the end of the last subBucket
          for (uint64_t counter = prefixSumForPositions[_SA[i]][subBucket];
               counter < prefixSumForPositions[_SA[i]][subBucket + 1];
               counter++) {
            if (counterSmallerThanHead[counter]) {
              if (prevChar != characterEqualToReference) {
                streamOutfile.write((char *)&runLength, sizeof(uint64_t));
                streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
                runLength = counterSmallerThanHead[counter];
                prevChar = characterEqualToReference;
              } else {
                runLength += counterSmallerThanHead[counter];
              }
              bucketsForExpandedBWT[i] += counterSmallerThanHead[counter];
            }
            auto x = BWTheads[headCounter++];
            if (x != prevChar) {
              streamOutfile.write((char *)&runLength, sizeof(uint64_t));
              streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
              runLength = 1;
              prevChar = x;
            } else {
              runLength++;
            }
            bucketsForExpandedBWT[i]++;
          }
          if (bucketsForExpandedBWT[i] != 0) {
            if (prevChar != characterEqualToReference) {
              streamOutfile.write((char *)&runLength, sizeof(uint64_t));
              streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
              runLength = -bucketsForExpandedBWT[i];
              prevChar = characterEqualToReference;
            } else {
              runLength += -bucketsForExpandedBWT[i];
            }
          }
        }
      }
    }
    streamOutfile.write((char *)&runLength, sizeof(uint64_t));
    streamOutfile.write((char *)&prevChar, sizeof(uint8_t));
    streamOutfile.close();
  }
  delete[] BWTheads;
  std::vector<uint32_t>().swap(setOfKeys);
  std::unordered_map<uint32_t, std::vector<uint64_t>>().swap(
      prefixSumForPositions);
  delete[] bucketsForExpandedBWT;
  delete[] counterSmallerThanHead;
  
}


void computeBWT(Args arg, std::string &refFileName, std::string &collFileName){
  std::cout << "==== Processing reference sequence" << std::endl;
  initialize_reference(arg, refFileName, collFileName, arg.prefixLength);
  std::cout << "==== Processing collection" << std::endl;
  if (_n < 1000000) {
    process_collection_small_reference(arg, collFileName);
  } else {
    process_collection_large_reference(arg, collFileName);
  }
}
