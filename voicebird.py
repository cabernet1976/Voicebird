import os
import stat
import shutil
import sys
import time
import socket
import struct
import re
import cPickle as pickle
import threading
import Queue
import select
import copy
from xml.dom import minidom


####################
# global consts
####################
VOICEBIRD_VERSION = 0.13
CIF_VERSION = 3
SUPPORT_PYTHON_VERSIONS = ('2.4', '2.5', '2.6', '2.7')

SNOOP_IDENTIFICATION_PATTERN_SNOOP = (0x73, 0x6E, 0x6F, 0x6F, 0x70, 0x00, 0x00, 0x00)
SNOOP_VERSION_NUMBER = 2
SNOOP_DATALINK_TYPE_ETHERNET = 4
ETHERNET_TYPE_IP = 0x800
IP_PROTOCOL_UDP = 17
SIP_PORTS = (5060, 5061)
PAYLOAD_TYPE_G711 = 0
PAYLOAD_TYPE_COMFORT_NOISE = 13
# private payload types for IVR autotest
PAYLOAD_TYPE_IVR_RECORD_FILE = 126
PAYLOAD_TYPE_IVR_PROMPT = 127

PROMPT_TYPE_SPEAK       = 1
PROMPT_TYPE_SYSTEM      = 2
PROMPT_TYPE_RECORD_TONE = 3

UDP_TYPE_UNKNOW                 = -1
UDP_TYPE_SIP                    = 0
UDP_TYPE_RTP                    = 1
UDP_TYPE_RTP_EVENT              = 2     # RFC 2833
UDP_TYPE_RTP_IVR_RECORD_FILE    = 3
UDP_TYPE_RTP_IVR_PROMPT         = 4
UDP_TYPE_RTP_IVR_SPEAK_PROMPT   = UDP_TYPE_RTP_IVR_PROMPT + PROMPT_TYPE_SPEAK          # in speak.vox
UDP_TYPE_RTP_IVR_SYSTEM         = UDP_TYPE_RTP_IVR_PROMPT + PROMPT_TYPE_SYSTEM         # in system32.vox
UDP_TYPE_RTP_IVR_RECORD_TONE    = UDP_TYPE_RTP_IVR_PROMPT + PROMPT_TYPE_RECORD_TONE    # record tone

SHORT_NAME_OF_IVR_EVENT = { UDP_TYPE_RTP_IVR_RECORD_FILE : 'r', \
                            UDP_TYPE_RTP_IVR_SPEAK_PROMPT : 'p', \
                            UDP_TYPE_RTP_IVR_SYSTEM : 's', \
                            UDP_TYPE_RTP_IVR_RECORD_TONE : 't'}

SIP_TYPE_UNKNOW = -1
SIP_TYPE_INVITE = 0
SIP_TYPE_ACK    = 1
SIP_TYPE_BYE    = 2

DEFAULT_SIP_PORT = 5060 # DON'T CHANGE IT EASILY
MAGIC_SIP_URI = 'cabernet1976@163.com:'+str(DEFAULT_SIP_PORT)
MAGIC_IP_AND_PORT = '127.0.0.1:'+str(DEFAULT_SIP_PORT)

MIN_UDP_LEN = 1024

# Regular Expression
RE_INT = re.compile(r'\d+')
RE_EMAIL = re.compile(r'\+*\w+([-+.]\w+)*@\w+([-.]\w+)*\.\w+([-.]\w+)*')
RE_SIP_URI = re.compile(r'\+*\w+([-+.]\w+)*@\w+([-.]\w+)*\.\w+([-.]\w+)* *: *\d+\b')
RE_IP = re.compile(r'\b(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\b')
RE_IP_AND_PORT = re.compile(r'\b(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.(25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\b *: *\d+\b')
RE_SIP_INVITE = re.compile(r'INVITE .+ SIP/2\.0')
RE_SIP_RESPONSE = re.compile(r'SIP/2\.0 +\d\d\d.*')
RE_SIP_RESPONSE_CODE = re.compile(r'\d\d\d')
RE_SIP_100 = re.compile(r'SIP/2\.0 +100.*')
RE_SIP_180 = re.compile(r'SIP/2\.0 +180.*')
RE_SIP_183 = re.compile(r'SIP/2\.0 +183.*')
RE_SIP_200 = re.compile(r'SIP/2\.0 +200.*')
RE_SIP_ACK = re.compile(r'ACK .+ SIP/2\.0')
RE_SIP_BYE = re.compile(r'BYE .+ SIP/2\.0')
RE_SIP_VIA = re.compile(r'Via *:.*SIP/2\.0/UDP.*')
RE_SIP_FROM = re.compile(r'From *:.*tag *=.*')
RE_SIP_FROM_DISPLAY = re.compile(r'".*"')
RE_SIP_TAG = re.compile(r'tag *= *\w+')
RE_SIP_TO = re.compile(r'To *: *.*')
RE_SIP_CALL_ID = re.compile(r'Call-ID *: *.*')
RE_SIP_CONTACT = re.compile(r'Contact *: *.*')
RE_SIP_CONTENT_LENGTH = re.compile(r'Content-Length *: *.*')
RE_SIP_CSEQ = re.compile(r'CSeq *: *\d+.*')
RE_SIP_ROUTE = re.compile(r'Route *: *.*')
RE_SIP_RECORD_ROUTE = re.compile(r'Record-Route *: *.*')
RE_SIP_DIVERSION = re.compile(r'Diversion *: *.*')
RE_SDP_V = re.compile(r'v=0\b')
RE_SDP_O = re.compile(r'o=.*')
RE_SDP_C = re.compile(r'c=.*')
RE_SDP_M = re.compile(r'm=.*')
RE_SDP_M_AUDIO = re.compile(r'audio +\d+')
RE_SDP_RTPMAP = re.compile(r'rtpmap *: *\d+\b')
RE_SDP_TELEPHONE_EVENT = re.compile(r'a=rtpmap:\d+ +telephone-event.*')

SIP_STATE_IDLE          = 0
SIP_STATE_WAITING_183   = 1
SIP_STATE_WAITING_200   = 2
SIP_STATE_BEFORE_ACK    = 3
SIP_STATE_AFTER_ACK     = 4
SIP_STATE_BYEING        = 5
SIP_STATE_BYED          = SIP_STATE_IDLE

DEFAULT_PARAMETER_PHONE = 'anonymous'
DEFAULT_PARAMETER_REASON = 'unknown'

LEFT_TO_RIGHT = True
RIGHT_TO_LEFT = False

TIME_ONE_TICK               = 0.005 # (second)
TIME_ONE_WINK               = 0.1   # (second)

MAX_TIME_TO_EXIT            = 15    # (second)
MIN_TIME_TO_EXIT            = 3     # (second)

ONE_UNIT_TIME_WAIT_TO_WORK  = 0.5   # (second)

PRINT_PANDING_LEFT          = 5
PRINT_IVR_EVENT_PANDING    = 10
PRINT_CENTER_WIDTH          = 58

SNOOP_FILE_EXT = '.snoop'
CASE_LIST_FILE_EXT = '.cl'
CASE_INFORMATION_FILE_EXT = '.cif'
DIALOG_PACKETS_LIST_FILE_EXT = '.dpl'

ITEM_TYPE_UNKNOWN                   = -1
ITEM_TYPE_START_WORK                = 0
ITEM_TYPE_SIP_DATA                  = 1
ITEM_TYPE_RTP_DATA                  = 2
ITEM_TYPE_SIGN_TO_KILL_THREAD       = 3
ITEM_TYPE_START_A_DIALOG            = 4
ITEM_TYPE_WRITE_TEST_RESULT         = 5
ITEM_TYPE_WRITE_UNPASSED_CALL_FLOW  = 6
ITEM_TYPE_WRITE_LOG                 = 7
ITEM_TYPE_GET_A_CASE_REQ            = 8
ITEM_TYPE_GET_A_CASE_ACK            = 9
ITEM_TYPE_HAVE_A_REST               = 10

#Note: the voicebird tag format: [prefix]F[fffff]C[ccccc]D[ddddd]A[timestamp]
#      fffff is X digitals channel index after 'F'
#      ccccc is X digitals case index after 'C'
#      ddddd is X digitals dialog index after 'D'
#      timestamp after 'A'
VOICEBIRD_TAG_PREFIX            = '701CEB19D'
LEN_OF_VOICEBIRD_TAG_PREFIX     = len(VOICEBIRD_TAG_PREFIX)
LEN_OF_VOICEBIRD_TAG_UNIT       = 5

RESULT_VALUE_UNKNOWN                = -1
RESULT_VALUE_FAIL                   = 0
RESULT_VALUE_SIP_ERROR              = 1
RESULT_VALUE_PASS                   = 2
RESULT_VALUE_PASS_BUT_UNCOMPLETED   = 3
RESULT_VALUE_PASS_BUT_DEFECTIVE_CASE= 4
RESULT_VALUE_IGNORE                 = 5
RESULT_VALUE_INTERRUPTED            = 6

RESULT_VALUE_STRINGS = {RESULT_VALUE_UNKNOWN : 'UNKNOW', \
                        RESULT_VALUE_FAIL : 'FAIL', \
                        RESULT_VALUE_SIP_ERROR : 'FAIL (SIP ERROR)', \
                        RESULT_VALUE_PASS : 'pass', \
                        RESULT_VALUE_PASS_BUT_UNCOMPLETED : 'pass (UNCOMPLETED)', \
                        RESULT_VALUE_PASS_BUT_DEFECTIVE_CASE : 'pass (DEFECTIVE CASE)', \
                        RESULT_VALUE_IGNORE : 'ignore', \
                        RESULT_VALUE_INTERRUPTED : 'interrupted'}

DIR_CONFIG                  = 'config'
CALL_PARAMETERS_CONFIG_FILE = '%s/parameters.dat' % (DIR_CONFIG)
FUZZY_PROMPTS_FILE          = '%s/fuzzyprompts.cfg' % (DIR_CONFIG)
BOOK_DB_FILE                = '%s/book.db' % (DIR_CONFIG)

DIR_TEST_RESULT             = 'log'
TEST_RESULT_FILE            = '%s/testresult' % (DIR_TEST_RESULT)
TEST_RESULT_FILE_EXT        = '.txt'

DIR_UNPASSED_CALL_FLOW      = 'log'
UNPASSED_CALL_FLOW_FILE     = '%s/unpassedcallflow' % (DIR_UNPASSED_CALL_FLOW)
UNPASSED_CALL_FLOW_FILE_EXT = '.txt'

DIR_LOG                     = 'log'
LOG_FILE                    = '%s/log' % (DIR_LOG)
LOG_FILE_EXT                = '.txt'

DIR_CASE                    = 'case'
DIR_CACHE                   = 'cache'

MAX_PROMPT_STR_LEN          = 80

ANNOTATION_CHAR = '#'

BACK_LINE_STR = '%c%c%c' % (27,'[','A')

# each IVR event will be sent so many times
IVR_EVENT_DUP_TIMES = 8

TEMPLATE_BYE = """BYE sip:[CALLED]@[DESTINATION]:%d SIP/2.0
Via: SIP/2.0/UDP [SOURCE];branch=z9hG4bKac1580b40000001e496580db00006f7c00000020;rport
Max-Forwards: 70
From: <sip:[FROM_CALLING]@[SOURCE]>;tag=[FROM_TAG]
To: <sip:[CALLED]@[DESTINATION]>;tag=[TO_TAG]
Call-ID: [FROM_TAG]@[SOURCE]
CSeq: 2 BYE
Content-Length: 0""" % (DEFAULT_SIP_PORT)

IVR_8250_SIGN = 'CW UC'

####################
# global variables
####################
# ...


class DialogPacket:
    """
    [Class]
    This is a struct used to transfer packet data from file to ChannelWorker
    """

    originalPacketIndex = -1
    dialogIndex = -1
    received = False    # whether this packet is received from destination
    timestamp = ''
    delttime = 0.0
    sourceIp = ''
    destinationIp = ''
    sourcePort = 0
    destinationPort = 0
    udpType = UDP_TYPE_UNKNOW
    sipType = SIP_TYPE_UNKNOW
    data = ''
    # Note: the following 3 fields can only get from the function SnoopParser.__readRtp()
    rtpTimestamp = 0
    dtmf = -1
    ivrEventStr = ''
    isTwin = False

    def __str__(self):
        tempStr = ''
        tempStr += ' originalPacketIndex: ' + str(self.originalPacketIndex) + '\n'
        tempStr += ' dialogIndex: ' + str(self.dialogIndex) + '\n'
        tempStr += ' received: ' + str(self.received) + '\n'
        tempStr += ' timestamp: ' + self.timestamp + '\n'
        tempStr += ' delttime: ' + str(self.delttime) + '\n'
        tempStr += ' sourceIp: ' + self.sourceIp + '\n'
        tempStr += ' destinationIp: ' + self.destinationIp + '\n'
        tempStr += ' sourcePort: ' + str(self.sourcePort) + '\n'
        tempStr += ' destinationPort: ' + str(self.destinationPort) + '\n'
        tempStr += ' udpType: ' + str(self.udpType) + '\n'
        tempStr += ' sipType: ' + str(self.sipType) + '\n'
        tempStr += ' rtpTimestamp: ' + str(self.rtpTimestamp) + '\n'
        tempStr += ' dtmf: ' + str(self.dtmf) + '\n'
        tempStr += ' ivrEventStr: ' + self.ivrEventStr + '\n'
        tempStr += ' isTwin: ' + str(self.isTwin) + '\n'
        tempStr += ' data: \n' + self.data
        return tempStr


class DialogNumber:
    """
    [Class]
    This is a struct used to save dialog's numbers
    """

    calledNumber = ''
    redirectNumber = ''
    callingNumber = ''

    def __init__(self, calledNumber, redirectNumber, callingNumber):
        self.calledNumber = calledNumber
        self.redirectNumber = redirectNumber
        self.callingNumber = callingNumber


    def __init__(self, calledNumber, callingNumber):
        self.calledNumber = calledNumber
        self.callingNumber = callingNumber


    def __str__(self):
        tempStr = ''
        tempStr += ' Called Number: ' + self.calledNumber + '\n'
        if len(self.redirectNumber)>0:
            tempStr += ' Redirect Number: ' + self.redirectNumber + '\n'
        tempStr += ' Calling Number: ' + self.callingNumber
        return tempStr


class CaseInformation:
    """
    [Class]
    This is a struct used to dump original case information to the .cif file
    """

    cifVersion = 0
    snoopFileName = ''
    snoopFileCreateTime = 0
    snoopFileSize = 0
    dialogNumbers = []

    def __str__(self):
        tempStr = ''
        tempStr += ' CIF Version: ' + self.cifVersion + '\n'
        tempStr += ' Snoop File Name: ' + self.snoopFileName + '\n'
        tempStr += ' Snoop File Create Time: ' + str(self.snoopFileCreateTime) + '\n'
        tempStr += ' Snoop File Size: ' + str(self.snoopFileSize) + '\n'
        for i in range(len(dialogNumbers)):
            tempStr += ' -- Dialog %d --\n' % (i+1)
            tempStr += str(number)
        return tempStr


class CaseData:
    """
    [Class]
    This is a struct used to save all needed data for a test case
    """

    snoopFileName = ''  # snoop file name
    cacheName = ''      # cache name which is CaseInformation and DialogPacketsList dump file name exclude ext name
                        # Note: it is not a special file name
    caseConfig = None   # object of CaseConfig


def tuple2Hex(t):
    """
    [Function]
    transform the items in tuple to hex format

    [Argument]
    t: a tuple

    [Return]
    a tuple whose items are hex format
    """

    if type(t) != type((0,)):
        return t

    h = []
    for x in t:
        h.append(hex(x))
    return tuple(h)


def getDtmfChar(dtmf):
    """
    [Function]
    transform dtmf value to print-able char

    [Argument]
    dtmf: dtmf value

    [Return]
    print-able dtmf char
    """

    if dtmf in range(0, 9+1):
        return str(dtmf)

    if dtmf==10:
        return '*'

    if dtmf==11:
        return '#'

    if dtmf in range(12, 15+1):
        return chr(ord('A')+dtmf-12)

    if dtmf==16:
        return 'Flash'


class QueueItem:
    """
    [Class]
    This is a struct used to save the data in the queue
    """

    itemType = ITEM_TYPE_UNKNOWN
    itemData = ''

    def __init__(self, type, data=''):
        self.itemType = type
        self.itemData = data


class QueueItemData4TestResult:
    """
    [Class]
    This is a struct used to save queue item data for test result
    """

    testResultValue = -1
    content = ''

    def __init__(self, testResultValue, content):
        self.testResultValue = testResultValue
        self.content = content


class QueueItemData4Resource:
    """
    [Class]
    This is a struct used to save queue item data for ResourceController
    """

    channelQueue = None
    gettingCacheName = ''
    releasingCacheName = ''

    def __init__(self, channelQueue, gettingCacheName, releasingCacheName):
        self.channelQueue = channelQueue
        self.gettingCacheName = gettingCacheName
        self.releasingCacheName = releasingCacheName


class InfoCollector(threading.Thread):
    """
    [Class]
    A thread used to collect information
    """

    logFlag = True

    def __init__(self, logFileName, logQueue, logFlag):
        """
        [Function]
        new a InfoCollector object

        [Argument]
        (N/A)
        """

        threading.Thread.__init__(self, name = 'InfoCollector')

        self.logFileName = logFileName
        self.logQueue = logQueue
        self.logFlag = logFlag

        self.firstTimePrintStatistic = True

        self.startTime = time.time()
        self.totalStartedDialogCount = 0
        self.totalEndedDialogCount = 0
        self.resultStatisticDict = {RESULT_VALUE_FAIL : 0, \
                                    RESULT_VALUE_SIP_ERROR : 0, \
                                    RESULT_VALUE_PASS : 0, \
                                    RESULT_VALUE_PASS_BUT_UNCOMPLETED : 0, \
                                    RESULT_VALUE_PASS_BUT_DEFECTIVE_CASE : 0}

        if self.logFlag:
            self.__prepareLogFile()
            self.__prepareTestResultFile()
            self.__prepareUnpassedCallFlowFile()


    def __prepareTestResultFile(self):
        """
        [Function]
        prepare test result file

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        tempDir = DIR_TEST_RESULT
        tempFile = TEST_RESULT_FILE
        tempExt = TEST_RESULT_FILE_EXT

        if not os.path.exists(tempDir):
            os.makedirs(tempDir)

        if os.path.exists(tempFile+tempExt):
            tempModificationTime = time.localtime(os.stat(tempFile+tempExt).st_mtime)
            shutil.move(tempFile+tempExt, tempFile+'.%d%02d%02d%02d%02d%02d' % (tempModificationTime[:6]))

        self.testResultFileObj = file(tempFile+tempExt, 'w')


    def __writeToTestResultFile(self, content):
        """
        [Function]
        write something to test result file

        [Argument]
        content: the writing content

        [Return]
        (N/A)
        """

        if self.logFlag:
            self.testResultFileObj.write(content)
            self.testResultFileObj.flush()


    def __prepareUnpassedCallFlowFile(self):
        """
        [Function]
        prepare unpassed call flows file

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        tempDir = DIR_UNPASSED_CALL_FLOW
        tempFile = UNPASSED_CALL_FLOW_FILE
        tempExt = UNPASSED_CALL_FLOW_FILE_EXT

        if not os.path.exists(tempDir):
            os.makedirs(tempDir)

        if os.path.exists(tempFile+tempExt):
            tempModificationTime = time.localtime(os.stat(tempFile+tempExt).st_mtime)
            shutil.move(tempFile+tempExt, tempFile+'.%d%02d%02d%02d%02d%02d' % (tempModificationTime[:6]))

        self.unpassedCallFlowFileObj = file(tempFile+tempExt, 'w')


    def __writeToUnpassedCallFlowFile(self, content):
        """
        [Function]
        write something to unpassed callflow file

        [Argument]
        content: the writing content

        [Return]
        (N/A)
        """

        if self.logFlag:
            self.unpassedCallFlowFileObj.write(content)
            self.unpassedCallFlowFileObj.flush()


    def __prepareLogFile(self):
        """
        [Function]
        prepare log file

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        tempDir = DIR_LOG
        tempFile = self.logFileName
        tempExt = LOG_FILE_EXT

        if not os.path.exists(tempDir):
            os.makedirs(tempDir)

        if os.path.exists(tempFile+tempExt):
            tempModificationTime = time.localtime(os.stat(tempFile+tempExt).st_mtime)
            shutil.move(tempFile+tempExt, tempFile+'.%d%02d%02d%02d%02d%02d' % (tempModificationTime[:6]))

        self.logFileObj = file(tempFile+tempExt, 'w')


    def __writeToLogFile(self, content):
        """
        [Function]
        write something to log file

        [Argument]
        content: the writing content

        [Return]
        (N/A)
        """

        if self.logFlag:
            self.logFileObj.write(content)
            self.logFileObj.flush()


    def __closeFiles(self):
        """
        [Function]
        close test result and log file

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        if self.logFlag:
            self.testResultFileObj.close()
            self.unpassedCallFlowFileObj.close()
            self.logFileObj.close()


    def __getStatistic(self):
        """
        [Function]
        get statistic

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        tempSeconds = time.time() - self.startTime
        if self.totalEndedDialogCount>0:
            tempFailPercentage = '%.2f%%' % (float(self.resultStatisticDict[RESULT_VALUE_FAIL]*100)/self.totalEndedDialogCount)
            tempFailPercentage = tempFailPercentage.rjust(7)
            tempSipErrorPercentage = '%.2f%%' % (float(self.resultStatisticDict[RESULT_VALUE_SIP_ERROR]*100)/self.totalEndedDialogCount)
            tempSipErrorPercentage = tempSipErrorPercentage.rjust(7)
            tempPassPercentage = '%.2f%%' % (float(self.resultStatisticDict[RESULT_VALUE_PASS]*100)/self.totalEndedDialogCount)
            tempPassPercentage = tempPassPercentage.rjust(7)
            tempPassButUncompleted = '%.2f%%' % (float(self.resultStatisticDict[RESULT_VALUE_PASS_BUT_UNCOMPLETED]*100)/self.totalEndedDialogCount)
            tempPassButUncompleted = tempPassButUncompleted.rjust(7)
            tempPassButDefectiveCase = '%.2f%%' % (float(self.resultStatisticDict[RESULT_VALUE_PASS_BUT_DEFECTIVE_CASE]*100)/self.totalEndedDialogCount)
            tempPassButDefectiveCase = tempPassButDefectiveCase.rjust(7)
        else:
            tempFailPercentage = '0.00%'.rjust(7)
            tempSipErrorPercentage = '0.00%'.rjust(7)
            tempPassPercentage = '0.00%'.rjust(7)
            tempPassButUncompleted = '0.00%'.rjust(7)
            tempPassButDefectiveCase = '0.00%'.rjust(7)


        tempStr  = """%s
   Started: %d (calls) / %d (seconds) = %.2f (CPS)
   Ended:   %d (calls)
 -------------------------------------------------------
  <result>                     <count>   <percentage>
 -------------------------------------------------------
   FAIL                  : %10d        %s
   FAIL (SIP ERROR)      : %10d        %s
   pass                  : %10d        %s
   pass (UNCOMPLETED)    : %10d        %s
   pass (DEFECTIVE CASE) : %10d        %s

""" % ( ' '*50, \
        self.totalStartedDialogCount, tempSeconds, float(self.totalStartedDialogCount)/tempSeconds, \
        self.totalEndedDialogCount, \
        self.resultStatisticDict[RESULT_VALUE_FAIL], tempFailPercentage, \
        self.resultStatisticDict[RESULT_VALUE_SIP_ERROR], tempSipErrorPercentage, \
        self.resultStatisticDict[RESULT_VALUE_PASS], tempPassPercentage, \
        self.resultStatisticDict[RESULT_VALUE_PASS_BUT_UNCOMPLETED], tempPassButUncompleted, \
        self.resultStatisticDict[RESULT_VALUE_PASS_BUT_DEFECTIVE_CASE], tempPassButDefectiveCase \
       )

        return tempStr


    def __printStatisticInScreen(self, statistic):
        """
        [Function]
        print statistic to screen

        [Argument]
        statistic: the printing statistic content

        [Return]
        (N/A)
        """

        global callParameters
        if callParameters.isStressTest:
            tempLineCount = statistic.count('\n')
            if self.firstTimePrintStatistic:
                # 2 == line count of 'Wait to start ...'
                sys.stdout.write(BACK_LINE_STR*2)
                self.firstTimePrintStatistic = False
            else:
                sys.stdout.write(BACK_LINE_STR*tempLineCount)
            sys.stdout.write((' '*60 + '\n')*tempLineCount)
            sys.stdout.write(BACK_LINE_STR*tempLineCount)
            sys.stdout.write(statistic)


    def run(self):
        """
        [Function]
        run InfoCollector

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        while True:
            tempItem = self.logQueue.get()
            if tempItem.itemType==ITEM_TYPE_SIGN_TO_KILL_THREAD:
                if self.totalEndedDialogCount>0:
                    self.__writeToTestResultFile(self.__getStatistic())
                self.__closeFiles()
                return
            #else:

            if tempItem.itemType==ITEM_TYPE_WRITE_LOG:
                self.__writeToLogFile(tempItem.itemData+'\n')
            elif tempItem.itemType==ITEM_TYPE_START_A_DIALOG:
                self.totalStartedDialogCount += 1
                self.__printStatisticInScreen(self.__getStatistic())
            elif tempItem.itemType==ITEM_TYPE_WRITE_TEST_RESULT:
                self.totalEndedDialogCount += 1
                self.resultStatisticDict[tempItem.itemData.testResultValue] += 1
                self.__writeToTestResultFile(tempItem.itemData.content+'\n')
                self.__printStatisticInScreen(self.__getStatistic())
            elif tempItem.itemType==ITEM_TYPE_WRITE_UNPASSED_CALL_FLOW:
                self.__writeToUnpassedCallFlowFile(tempItem.itemData+'\n')


LOG_QUEUE = Queue.Queue()
class Log:
    """
    [Class]
    A well use client class for InfoCollector
    """

    onlyLog = False
    logFlag = True

    def __prepareLogFile(self):
        """
        [Function]
        prepare log file

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        if not self.logFlag: return

        tempDir = DIR_LOG
        tempFile = self.logFileName
        tempExt = LOG_FILE_EXT

        if not os.path.exists(tempDir):
            os.makedirs(tempDir)

        if os.path.exists(tempFile+tempExt):
            tempModificationTime = time.localtime(os.stat(tempFile+tempExt).st_mtime)
            shutil.move(tempFile+tempExt, tempFile+'.%d%02d%02d%02d%02d%02d' % (tempModificationTime[0:6]))

        self.logFileObj = file(tempFile+tempExt, 'w')


    def __writeToLogFile(self, content):
        """
        [Function]
        write something to log file

        [Argument]
        content: the writing content

        [Return]
        (N/A)
        """

        if self.logFlag:
            self.logFileObj.write(content)
            self.logFileObj.flush()


    def __closeLogFile(self):
        if self.logFlag:
            self.logFileObj.close()


    def __init__(self, logFileName, onlyLog):
        # PARAMETER -nd: No Debug, means not to write debug log to file
        if '-nd' in sys.argv:
            self.logFlag = False

        self.logFileName = logFileName
        self.onlyLog = onlyLog

        if onlyLog:
            self.__prepareLogFile()
        else:
            global LOG_QUEUE
            global LOG_PRINTER
            LOG_PRINTER = InfoCollector(logFileName, LOG_QUEUE, self.logFlag)
            LOG_PRINTER.setDaemon(True)
            LOG_PRINTER.start()


    def __del__(self):
        if self.onlyLog:
            self.__closeLogFile()


    def startADialog(self):
        """
        [Function]
        tell that a dialog is starting

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """
        if self.onlyLog: return

        global LOG_QUEUE
        LOG_QUEUE.put(QueueItem(ITEM_TYPE_START_A_DIALOG))


    def writeTestResult(self, resultValue, content):
        """
        [Function]
        write test result

        [Argument]
        resultValue: result value
        content: log content

        [Return]
        (N/A)
        """
        if self.onlyLog: return

        global LOG_QUEUE
        tempData = QueueItemData4TestResult(resultValue, content)
        LOG_QUEUE.put(QueueItem(ITEM_TYPE_WRITE_TEST_RESULT, tempData))


    def writeUnpassedCallFlow(self, content):
        """
        [Function]
        write unpassed call flow

        [Argument]
        content: log content

        [Return]
        (N/A)
        """
        if self.onlyLog: return

        global LOG_QUEUE
        LOG_QUEUE.put(QueueItem(ITEM_TYPE_WRITE_UNPASSED_CALL_FLOW, content))


    def writeLog(self, content):
        """
        [Function]
        write log

        [Argument]
        content: log content

        [Return]
        (N/A)
        """
        if self.onlyLog:
            self.__writeToLogFile(content+'\n')
        else:
            global LOG_QUEUE
            LOG_QUEUE.put(QueueItem(ITEM_TYPE_WRITE_LOG, str(content)))


    def a(self, content):
        """
        [Functon]
        write assert log
        Note: assert information will be printed in the screen

        [Argument]
        content: log content

        [Return]
        (N/A)
        """
        self.writeLog('ASSERT: '+str(content))
        print str(content)


    def e(self, content):
        """
        [Function]
        write error log

        [Argument]
        content: log content

        [Return]
        (N/A)
        """
        self.writeLog('ERROR: '+str(content))


    def i(self, content):
        """
        [Function]
        write info(rmation) log

        [Argument]
        content: log content

        [Return]
        (N/A)
        """
        self.writeLog('INFO: '+str(content))


    def w(self, content):
        """
        [Function]
        write warn(ing) log

        [Argument]
        content: log content

        [Return]
        (N/A)
        """
        self.writeLog('WARN: '+str(content))


def createLogObj(logFileName=LOG_FILE, onlyLog=False):
    global LOG
    LOG = Log(logFileName, onlyLog)


def deleteLogObj():
    global LOG_QUEUE
    LOG_QUEUE.put(QueueItem(ITEM_TYPE_SIGN_TO_KILL_THREAD))


def setGlobalLogObj(theGlobalLogObj):
    global LOG
    LOG = theGlobalLogObj


class ResourceItem:
    """
    [Class]
    A struct to save resource information
    """
    dialogPacketsList = None
    timeToLoad = -1
    linkCounter = 0

    def __init__(self, dpl):
        self.dialogPacketsList = dpl
        self.timeToLoad = time.time()
        self.linkCounter = 1


    def addLink(self):
        self.linkCounter += 1


    def deleteLink(self):
        self.linkCounter -= 1
        return self.linkCounter


    def getDpl(self):
        return self.dialogPacketsList


    def getLinkCount(self):
        return self.linkCounter


class ResourceController(threading.Thread):
    """
    [Class]
    A thread used to manage the resource, specially for DialogPacketsList
    """

    resourceDict = {}   # key: caseName, value: ResourceItem

    def __init__(self, resourceQueue):
        threading.Thread.__init__(self, name = 'ResourceController')
        self.resourceQueue = resourceQueue


    def run(self):
        """
        [Function]
        run ResourceController

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        while True:
            tempItem = self.resourceQueue.get()
            if tempItem.itemType==ITEM_TYPE_SIGN_TO_KILL_THREAD:
                return
            #else:

            if tempItem.itemType==ITEM_TYPE_GET_A_CASE_REQ:
                tempQueueItem = tempItem.itemData
                tempChannelQueue = tempQueueItem.channelQueue
                tempGettingCacheName = tempQueueItem.gettingCacheName
                tempReleasingCacheName = tempQueueItem.releasingCacheName

                try:
                    tempGettingResourceItem = self.resourceDict[tempGettingCacheName]
                    tempGettingResourceItem.addLink()
                    tempDpl = tempGettingResourceItem.getDpl()
                except KeyError:
                    tempDpl = loadDialogPacketsListFromCache(tempGettingCacheName)
                    tempGettingResourceItem = ResourceItem(tempDpl)
                    self.resourceDict[tempGettingCacheName] = tempGettingResourceItem

                if tempReleasingCacheName!='':
                    try:
                        tempReleasingResourceItem = self.resourceDict[tempReleasingCacheName]
                        if tempReleasingResourceItem.deleteLink()<=0:
                            self.resourceDict.pop(tempReleasingCacheName)
                            LOG.i("'%s' is removed from resourceDict" % (tempReleasingCacheName))
                    except KeyError:
                        LOG.w("Cannot find this cacheName '%s' in resourceDict to release" % (tempReleasingCacheName))

                tempChannelQueue.put(QueueItem(ITEM_TYPE_GET_A_CASE_ACK, tempDpl))


class IvrEventItem:
    """
    [Class]
    A struct used to save IVR event information
    """

    udpType = UDP_TYPE_UNKNOW
    ivrEventStr = ''

    def __init__(self, udpType, ivrEventStr='(any)'):
        self.udpType = udpType
        self.ivrEventStr = ivrEventStr

    def __str__(self):
        tempStr = ''
        tempStr += ' udpType: ' + str(self.udpType)
        tempStr += ' ivrEventStr: ' + self.ivrEventStr

        return tempStr


class ChannelWorker(threading.Thread):
    """
    [Class]
    A thread used to:
    1. manage SIP state machine
    2. send/receive RTP packet
    3. judge the case's result
    """

    # channel data
    channelIndex = -1           # Each ChannelWorker thread use an own unique channel index
    caseIndex = -1              # currently which case is in use, the caseIndex is the index in Distributor's caseList
    dialogIndex = 0             # currently which dialog in this case is calling
    sipState = SIP_STATE_IDLE
    called = ''
    calling = ''
    redirect = ''
    reason = ''
    fromTag = ''
    toTag = ''
    callId = ''
    sessionDestinationPort = 0
    baseTimeForRtp = 0.0
    telephoneEventPt = None
    ack = ''
    rtpTransport = 0

    hasStarted = False
    dialogPacketsList = None
    packetIndex = 0             # packet index in the dialog
    passed = True

    cachedCallFlow = ''
    cachedRtpTimestamp = -1
    cachedIvrEventStr = ''
    ignoredIvrEventCount = 0

    expectedMatchingPromptsList = []
    matchingIndex = 0

    nextInviteInSameCase = False

    is8250 = False


    def __init__(self, channelIndex, caseList, sipTransport, channelQueue, resourceQueue):
        """
        [Function]
        new a ChannelWorker object

        [Argument]
        sipTransport: SIP transport used to send SIP message
        channelQueue: Distributor use this queue to transfer data to ChannelWorker
        caseList: case data list
        """

        threading.Thread.__init__(self, name = 'ChannelWorker')

        self.cachedRtpTimestampFor2833 = 0

        self.channelIndex = channelIndex
        self.caseList = caseList
        self.sipTransport = sipTransport
        self.channelQueue = channelQueue
        self.resourceQueue = resourceQueue

        # dispersion to use the numbers
        if callParameters.calledCount>callParameters.channelCount:
            self.minCalledIndex = int(channelIndex * callParameters.calledCount / callParameters.channelCount)
            self.maxCalledIndex = int((channelIndex+1) * callParameters.calledCount / callParameters.channelCount) - 1
        else:
            self.maxCalledIndex = self.minCalledIndex = channelIndex%callParameters.calledCount
        #LOG.writeLog('eeee channel: %d, minCalledIndex: %d, maxCalledIndex: %d' % (self.channelIndex, self.minCalledIndex, self.maxCalledIndex))
        if callParameters.redirectCount>callParameters.channelCount:
            self.minRedirectIndex = int(channelIndex * callParameters.redirectCount / callParameters.channelCount)
            self.maxRedirectIndex = int((channelIndex+1) * callParameters.redirectCount / callParameters.channelCount) - 1
        else:
            if callParameters.redirectCount<=0:
                self.maxRedirectIndex = self.minRedirectIndex = 0
            else:
                self.maxRedirectIndex = self.minRedirectIndex = channelIndex%callParameters.redirectCount

        self.calledIndex = self.minCalledIndex
        self.redirectedIndex = self.minRedirectIndex

        # PARAMETER -nf: No call Flow, means not to draw the call flow to the screen
        self.willDrawCallFlow = (not callParameters.isStressTest) and ('-nf' not in sys.argv)

        self.timeLeftToStartWork = self.channelIndex * ONE_UNIT_TIME_WAIT_TO_WORK

        # create local RTP transport
        self.rtpTransport = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.rtpTransport.bind(('', 0))
        self.rtpTransport.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        #print 'self.rtpTransport.getsockname():', self.rtpTransport.getsockname()

        # PARAMETER -8250: the destination is 8250
        if '-8250' in sys.argv:
            self.is8250 = True


    def getLocalRtpTransport(self):
        """
        [Function]
        return RTP transport

        [Argument]
        (N/A)

        [Return]
        the socket connect of the RTP transport
        """
        return self.rtpTransport


    def __getResultStr(self, udpType, ivrEventStr):
        """
        [Function]
        get the expected or testing test result string

        [Argument]
        udpType: UDP type
        ivrEventStr: IVR event string

        [Return]
        the print-able test result
        """
        return '(%s) %s' % (SHORT_NAME_OF_IVR_EVENT[udpType], ivrEventStr)


    def __gotoNextIvrEvent(self):
        """
        [Function]
        move the pointer to the next IVR event in dialogPacketsList

        [Argument]
        (N/A)

        [Result]
        return True when getting the next IVR event, otherwise return False
        """

        while True:
            if self.packetIndex>=len(self.dialogPacketsList[self.dialogIndex]):
                return False

            tempPacket = self.dialogPacketsList[self.dialogIndex][self.packetIndex]

            if tempPacket.received:
                return True
            else:
                self.packetIndex += 1


    def __matchTwoPrompts(self, prompt1, prompt2):
        """
        [Function]
        match two prompts according to the fuzzy prompts dict

        [Parameter]
        two prompt names with length 7 (i.e. e1ja348) or 5 (i.e. ja348)

        [Return]
        if matched return True, otherwise return False
        """

        if prompt1==prompt2:
            return True

        try:
            tempPromptsPair = fuzzyPromptsDict[prompt1]
        except KeyError:
            return False
        else:
            try:
                tempPromptsPair.index(prompt2)
            except ValueError:
                return False
            else:
                return True


    def __fuzzyMatchPrompts(self, eventStrInPacket, eventStrReceived):
        """
        [Function]
        match promts in fuzzy

        [Parameter]
        eventStrInPacket: event string in packet
        eventStrReceived: event string received

        [Return]
        matched return True, otherwise return False
        """

        tempPromptNameInPacket = eventStrInPacket[eventStrInPacket.replace('\\', '/').rfind('/')+1:].lower()
        tempPromptNameInPacketWithoutLanguage = tempPromptNameInPacket[2:]

        tempPromptNameReceived = eventStrReceived[eventStrReceived.replace('\\', '/').rfind('/')+1:].lower()
        tempPromptNameReceivedWithoutLanguage = tempPromptNameReceived[2:]

        if self.__matchTwoPrompts(tempPromptNameInPacket, tempPromptNameReceived):
            return True
        else:
            return self.__matchTwoPrompts(tempPromptNameInPacketWithoutLanguage, tempPromptNameReceivedWithoutLanguage)


    def __smartJudge(self, receivedPayloadType, receivedExtendedData, expectedUdpType, expectedEventStr):
        """
        [Function]
        compare the packets in dialogPacketsList and received from IVR to judge whether this test step is passed

        [Argument]
        receivedPayloadType: received RTP's payload type
        receivedExtendedData: received RTP's extended data
        expectedUdpType: expected UDP type
        expectedEventStr: expected IVR event string

        [Return]
        return a tuple which has 3 items:
        1st item: whehter the judge result is passed
        2nd item: the expected result information
        3rd item: the testing result information
        4th item: expected prompt content
        5th item: testing result prompt content
        """

        tempExpectedResult = self.__getResultStr(expectedUdpType, expectedEventStr)

        tempExpectedPromptStr = ''
        tempUdpType,tempPromptId = washIvrPromptStr(expectedEventStr, expectedUdpType)
        tempPromptContent = getPromptContentById(tempPromptId)
        if tempUdpType==UDP_TYPE_RTP_IVR_SPEAK_PROMPT:
            if tempPromptId!='sil':     # forget silent indication
                tempExpectedPromptStr = '%s: %s' % (tempPromptId, tempPromptContent)
        else:
            tempExpectedResult = self.__getResultStr(tempUdpType, expectedEventStr)

        if receivedPayloadType==PAYLOAD_TYPE_IVR_RECORD_FILE:
            # only judge type when it is a Record File
            tempTestingResult = self.__getResultStr(UDP_TYPE_RTP_IVR_RECORD_FILE, receivedExtendedData)
            if expectedUdpType == UDP_TYPE_RTP_IVR_RECORD_FILE:
                return (True, tempExpectedResult, tempTestingResult, tempExpectedPromptStr, '')
            else:
                return (False, tempExpectedResult, tempTestingResult, tempExpectedPromptStr, '')
        elif receivedPayloadType==PAYLOAD_TYPE_IVR_PROMPT:
            if receivedExtendedData[0] == PROMPT_TYPE_SYSTEM:
                # only judge type when it is a System Prompt
                tempTestingResult = self.__getResultStr(UDP_TYPE_RTP_IVR_SYSTEM, receivedExtendedData[1])
                if expectedUdpType == UDP_TYPE_RTP_IVR_SYSTEM:
                    return (True, tempExpectedResult, tempTestingResult, tempExpectedPromptStr, '')
                else:
                    return (False, tempExpectedResult, tempTestingResult, tempExpectedPromptStr, '')
            elif receivedExtendedData[0] == PROMPT_TYPE_RECORD_TONE:
                # record tone need exactly judge
                tempTestingResult = self.__getResultStr(UDP_TYPE_RTP_IVR_RECORD_TONE, receivedExtendedData[1])
                if expectedUdpType == UDP_TYPE_RTP_IVR_RECORD_TONE:
                    return (True, tempExpectedResult, tempTestingResult, tempExpectedPromptStr, '')
                else:
                    return (False, tempExpectedResult, tempTestingResult, tempExpectedPromptStr, '')
            elif receivedExtendedData[0] == PROMPT_TYPE_SPEAK:
                # speak prompt will do fuzzy match when exactly judge failed
                tempTestingResult = self.__getResultStr(UDP_TYPE_RTP_IVR_SPEAK_PROMPT, receivedExtendedData[1])

                tempResultPromptStr = ''
                tempUdpType,tempPromptId = washIvrPromptStr(receivedExtendedData[1])
                tempPromptContent = getPromptContentById(tempPromptId)
                if tempUdpType==UDP_TYPE_RTP_IVR_SPEAK_PROMPT:
                    if tempPromptId!='sil':     # forget silent indication
                        tempResultPromptStr = '%s: %s' % (tempPromptId, tempPromptContent)
                else:
                    tempTestingResult = self.__getResultStr(tempUdpType, receivedExtendedData[1])

                if expectedUdpType == UDP_TYPE_RTP_IVR_SPEAK_PROMPT \
                        and (expectedEventStr==receivedExtendedData[1] \
                            or self.__fuzzyMatchPrompts(expectedEventStr, receivedExtendedData[1])):
                    return (True, tempExpectedResult, tempTestingResult, tempExpectedPromptStr, tempResultPromptStr)
                else:
                    return (False, tempExpectedResult, tempTestingResult, tempExpectedPromptStr, tempResultPromptStr)
            else:
                LOG.a('Unsupport prompt type %d' % (receivedExtendedData[0]))
                raise
        else:
            LOG.a('Unsupport payload type %d' % receivedPayloadType)
            raise


    def __processForNoPacketLeft(self, receivedPayloadType, receivedExtendedData):
        """
        [Function]
        specially process when no packet left for this dialog in dialogPacketsList

        [Argument]
        receivedPayloadType: received RTP's payload type
        receivedExtendedData: received RTP's extended data

        [Return]
        (N/A)
        """

        #print 'self.dialogIndex:', self.dialogIndex, ', self.packetIndex:', self.packetIndex

        if receivedPayloadType==PAYLOAD_TYPE_IVR_RECORD_FILE:
            self.__drawIvrEvent(RESULT_VALUE_FAIL, '(N/A)', '(f) '+receivedExtendedData)
        elif receivedPayloadType==PAYLOAD_TYPE_IVR_PROMPT:
            if receivedExtendedData[0] == PROMPT_TYPE_SYSTEM:
                self.__drawIvrEvent(RESULT_VALUE_FAIL, '(N/A)', '(s) '+receivedExtendedData[1])
            elif receivedExtendedData[0] == PROMPT_TYPE_RECORD_TONE:
                self.__drawIvrEvent(RESULT_VALUE_FAIL, '(N/A)', '(r) '+receivedExtendedData[1])
            elif receivedExtendedData[0] == PROMPT_TYPE_SPEAK:
                tempUdpType,tempPromptId = washIvrPromptStr(receivedExtendedData[1])
                if tempUdpType==UDP_TYPE_RTP_IVR_SPEAK_PROMPT:
                    if tempPromptId!='sil':     # forget silent indication
                        self.__drawIvrEvent(RESULT_VALUE_FAIL, '(N/A)', '(p) '+receivedExtendedData[1], '', '%s: %s' % (tempPromptId,getPromptContentById(tempPromptId)))
                        return

                self.__drawIvrEvent(RESULT_VALUE_FAIL, '(N/A)', '(p) '+receivedExtendedData[1])
            else:
                LOG.a('Unknown prompt type %d' % (receivedExtendedData[0]))
                raise
        else:
            LOG.a('Unsupport payload type %d' % (receivedPayloadType))
            raise


    def __hasCompleted(self):
        """
        [Function]
        scan the dialogPacketsList to check wheter current dialog is completed

        [Argument]
        (N/A)

        [Return]
        return True if current dialog is completed, otherwise return False
        """

        i = self.packetIndex+1  # Only need to check the packets behind current packet
        while True:
            if i>=len(self.dialogPacketsList[self.dialogIndex]):
                # All packets in this dialog have been done
                return True
            packet = self.dialogPacketsList[self.dialogIndex][i]
            if packet.dialogIndex!=self.dialogIndex:
                # All packets in this dialog have been done
                return True
            elif packet.dialogIndex==self.dialogIndex and packet.received==True:
                # Still exists message from destination
                return False
            else:
                i += 1


    def __drawCallFlowHeader(self, caseInfo, callerCalled):
        """
        [Function]
        draw call flow's header information

        [Argument]
        caseInfo: the case's information
        callerCalled: the caller and called

        [Return]
        (N/A)
        """

        tempStr = '\n[%s]\n' % (caseInfo)
        tempStr += ' '*int(PRINT_PANDING_LEFT/2) + callerCalled

        #tempStr += '\n' + str(time.localtime(time.time()))

        if self.willDrawCallFlow:
            print tempStr

        self.cachedCallFlow = tempStr + '\n'


    def __drawCallFlow(self, direction, description):
        """
        [Function]
        draw call flow

        [Argument]
        direction: LEFT_TO_RIGHT or RIGHT_TO_LEFT
        description: description about the piece of call flow

        [Return]
        (N/A)
        """

        tempStr = ' '*PRINT_PANDING_LEFT + '|' + description.center(PRINT_CENTER_WIDTH) + '|' + '\n'
        if direction==LEFT_TO_RIGHT:
            tempStr += ' '*PRINT_PANDING_LEFT + '|' + '-'*(PRINT_CENTER_WIDTH-1) + '>|'
        else:
            tempStr += ' '*PRINT_PANDING_LEFT + '|<' + '-'*(PRINT_CENTER_WIDTH-1) + '|'

        #tempStr += '\n' + str(time.localtime(time.time()))

        if self.willDrawCallFlow:
            print tempStr

        self.cachedCallFlow += tempStr + '\n'


    def __drawIvrEvent(self, resultValue, expect, result, expectPrompt='', resultPrompt=''):
        """
        [Function]
        draw special private event from IVR

        [Argument]
        resultValue: information to indicate pass, fail or something else
        expect: the expected result description
        result: the testing result description

        [Return]
        (N/A)
        """

        if expect and result:
            tempStr = ' '*PRINT_PANDING_LEFT + '|' + (' '*PRINT_IVR_EVENT_PANDING + RESULT_VALUE_STRINGS[resultValue]).ljust(PRINT_CENTER_WIDTH) + '|' + '\n'

            tempExpectPromptStr = expectPrompt
            if len(tempExpectPromptStr)>0:
                if len(tempExpectPromptStr)>MAX_PROMPT_STR_LEN:
                    tempExpectPromptStr = tempExpectPromptStr[:MAX_PROMPT_STR_LEN] + '[...]'

            tempResultPromptStr = resultPrompt
            if len(tempResultPromptStr)>0:
                if len(tempResultPromptStr)>MAX_PROMPT_STR_LEN:
                    tempResultPromptStr = tempResultPromptStr[:MAX_PROMPT_STR_LEN] + '[...]'

            tempStr += ' '*PRINT_PANDING_LEFT + '|' + (' '*(PRINT_IVR_EVENT_PANDING+4) + 'Expect: ' + expect).ljust(PRINT_CENTER_WIDTH) + '|  ' + tempExpectPromptStr + '\n'
            tempStr += ' '*PRINT_PANDING_LEFT + '|' + (' '*(PRINT_IVR_EVENT_PANDING+4) + 'Result: ' + result).ljust(PRINT_CENTER_WIDTH) + '|  ' + tempResultPromptStr + '\n'
            tempStr += ' '*PRINT_PANDING_LEFT + '|<' + '-'*(PRINT_CENTER_WIDTH-1) + '|'

            if self.willDrawCallFlow:
                print tempStr

            self.cachedCallFlow += tempStr + '\n'


    def __drawCallFlowSummary(self, resultValue=None):
        """
        [Function]
        draw call flow's summary

        [Argument]
        resultValue: information to indicate pass, fail or something else

        [Return]
        (N/A)
        """

        # 1. Get the last test result
        if resultValue:
            tempResultValue = resultValue
        else:
            tempResultValue = RESULT_VALUE_UNKNOWN
            if self.passed:
                if self.__hasCompleted():
                    tempResultValue = RESULT_VALUE_PASS
                else:
                    tempResultValue = RESULT_VALUE_PASS_BUT_UNCOMPLETED
            else:
                tempResultValue = RESULT_VALUE_FAIL

        snoopFileName = self.caseList[self.caseIndex].snoopFileName
        caseIndex = self.caseIndex
        dialogIndex = self.dialogIndex

        # 2. Draw call flow to the screen
        tempStr = 'RESULT: ' + RESULT_VALUE_STRINGS[tempResultValue] + '\n'
        if self.willDrawCallFlow:
            print tempStr

        self.cachedCallFlow += tempStr + '\n'

        # don't save interrupted callflow to file
        if tempResultValue==RESULT_VALUE_INTERRUPTED:
            return
        #else:

        # 3. Write test result
        tempStamp = str(self.channelIndex)
        now = time.localtime(time.time())
        tempStamp += '.%d%02d%02d%02d%02d%02d' % (now[0:6])
        tempLogStr = '[%s] Case %d: %s, Dialog: %d. SUMMARY: %s' % \
                    (tempStamp, caseIndex+1, snoopFileName, dialogIndex+1, RESULT_VALUE_STRINGS[tempResultValue])
        LOG.writeTestResult(tempResultValue, tempLogStr)

        # 4. Write unpassed call flow to unpassedcallflow.txt
        if tempResultValue!=RESULT_VALUE_PASS:
            LOG.writeUnpassedCallFlow('##### %s #####%s' % (tempStamp, self.cachedCallFlow))


    def __receiveRtp(self, queueData):
        """
        [Function]
        used to receive RTP message

        [Argument]
        queueData: the data received

        [Return]
        return True means NOT to continue dealing with packets in the list, otherwise return False
        """

        # Note: Distributor has filter the payload type
        tempPayloadType,tempRtpTimestamp,tempExtendedData = parseRtp(queueData, self.telephoneEventPt)
        tempIvrEventStr = ''
        if tempPayloadType==PAYLOAD_TYPE_IVR_RECORD_FILE:
            tempExtendedDataItems = [tempExtendedData,]
            tempIvrEventStr = tempExtendedData
        elif tempPayloadType==PAYLOAD_TYPE_IVR_PROMPT:
            tempExtendedDataItems = tempExtendedData
            tempIvrEventStr = str(tempExtendedData)
        else:
            LOG.a('Unsupport payload type ' + str(tempPayloadType))
            raise

        if self.__isDuplicatedIvrEvent(tempRtpTimestamp, tempIvrEventStr):
            return True

        for item in tempExtendedDataItems:
            tempGotNextIvrEvent = self.__gotoNextIvrEvent()
            # Note: don't deal with BYE, for it is the last message from IVR
            # tempGotNextIvrRtpEvent means whether got a IVR RTP event, but tempGotNextIvrEvent includes RTP and SIP
            tempGotNextIvrRtpEvent = tempGotNextIvrEvent
            if tempGotNextIvrEvent:
                tempPacket = self.dialogPacketsList[self.dialogIndex][self.packetIndex]
                if tempPacket.udpType==UDP_TYPE_SIP and tempPacket.sipType==SIP_TYPE_BYE:
                    self.packetIndex -= 1
                    tempGotNextIvrRtpEvent = False

            if tempGotNextIvrRtpEvent:
                tempPassed,tempExpect,tempResult,tempExpectPrompt,tempResultPrompt = \
                        self.__smartJudge(tempPayloadType, item, tempPacket.udpType, tempPacket.ivrEventStr)

                if tempPassed:
                    self.passed &= True
                    self.__drawIvrEvent(RESULT_VALUE_PASS, tempExpect, tempResult, tempExpectPrompt, tempResultPrompt)
                    self.packetIndex += 1
                else:
                    self.passed &= False
                    self.__drawIvrEvent(RESULT_VALUE_FAIL, tempExpect, tempResult, tempExpectPrompt, tempResultPrompt)
                    self.packetIndex += 1
            else:
                self.__processForNoPacketLeft(tempPayloadType, item)
                self.passed = False

        return False


    def __isDuplicatedIvrEvent(self, receivedRtpTimestamp, receivedIvrEventStr):
        """
        [Function]
        check whether this IVR event is duplicated

        [Argument]
        receivedRtpTimestamp: received RTP's timestamp
        receivedIvrEventStr: received IVR Event's content

        [Return]
        return True if duplicated, otherwise return False
        """

        if receivedRtpTimestamp!=0:
            # 1. only need checking duplication when autotest=2
            # 2.1. the ivr event == the cached
            # 2.2. the timestamp <= the cached
            # 2.3. don't ignore the event whose timestamp is the same as the previous one
            if receivedIvrEventStr==self.cachedIvrEventStr \
                    and receivedRtpTimestamp<=self.cachedRtpTimestamp \
                        and self.ignoredIvrEventCount<IVR_EVENT_DUP_TIMES:
                self.ignoredIvrEventCount += 1
                return True
            else:
                self.cachedRtpTimestamp = receivedRtpTimestamp
                self.cachedIvrEventStr = receivedIvrEventStr
                self.ignoredIvrEventCount = 0
                return False
        else:
            return False


    def run(self):
        """
        [Function]
        run ChannelWorker

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        while True:
            # 1. Get message from Distributor

            try:
                tempItem = self.channelQueue.get_nowait()
                #print 'itemType:', tempItem.itemType
            except KeyboardInterrupt:
                raise KeyboardInterrupt
            except:
                # Sleep then go on to deal with dialogPacketsList
                time.sleep(TIME_ONE_TICK)
            else:
                # Deal with message from Distributor, after that go on to deal with dialogPacketsList
                if tempItem.itemType==ITEM_TYPE_SIGN_TO_KILL_THREAD:
                    # send BYE then exit the thread
                    if self.sipState!=SIP_STATE_IDLE:
                        self.__sayGoodBye()
                    self.sipState = SIP_STATE_BYED
                    return
                elif tempItem.itemType==ITEM_TYPE_START_WORK:
                    # postpone starting work
                    if not self.hasStarted:
                        if self.timeLeftToStartWork>0:
                            self.timeLeftToStartWork -= ONE_UNIT_TIME_WAIT_TO_WORK
                            time.sleep(ONE_UNIT_TIME_WAIT_TO_WORK)
                            self.channelQueue.put(QueueItem(ITEM_TYPE_START_WORK))
                        else:
                            self.hasStarted = True
                            self.__startDialog()
                    else:
                        LOG.e('The channel worker has started work, do not ask start twice')
                    continue
                elif tempItem.itemType==ITEM_TYPE_GET_A_CASE_ACK:
                    self.dialogPacketsList = tempItem.itemData
                    self.__sendInvite()
                    continue
                elif tempItem.itemType==ITEM_TYPE_SIP_DATA:
                    if self.__receiveSip(tempItem.itemData):
                        time.sleep(TIME_ONE_TICK)
                        continue
                elif tempItem.itemType==ITEM_TYPE_RTP_DATA:
                    if self.__receiveRtp(tempItem.itemData):
                        time.sleep(TIME_ONE_TICK)
                        continue

            # 2. Process dialogPacketList

            # ChannelWorker doesn't work yet
            if not self.dialogPacketsList:
                time.sleep(TIME_ONE_WINK)
                continue

            # go through dialogPacketList only in this state
            if self.sipState!=SIP_STATE_AFTER_ACK:
                time.sleep(TIME_ONE_WINK)
                continue

            # No packet left in dialogPacketsList
            if self.packetIndex >= len(self.dialogPacketsList[self.dialogIndex]):
                time.sleep(TIME_ONE_WINK)
                continue

            packet = self.dialogPacketsList[self.dialogIndex][self.packetIndex]
            if packet.dialogIndex<self.dialogIndex:
                # Locate to the position of current dialog
                self.packetIndex += 1
                continue
            if packet.dialogIndex>self.dialogIndex:
                # Overflow the current dialog
                time.sleep(TIME_ONE_TICK*5)
                continue

            # 8250's sip stack send BYE in different port to INVITE's
            if self.is8250:
                if packet.udpType==UDP_TYPE_SIP and packet.sipType==SIP_TYPE_BYE:
                    self.sipState = SIP_STATE_BYED

                    self.__drawCallFlow(RIGHT_TO_LEFT, '(no waiting for 8250 BYE)')
                    self.__drawCallFlowSummary()
                    self.__restBeforeNextDialog(TIME_ONE_WINK*5)
                    self.__startDialog(self.caseIndex, self.dialogIndex+1)
                    continue

            # This is a received packet, let it be and continue waiting for message from Distributor
            if packet.received:
                time.sleep(TIME_ONE_TICK*5)
                continue

            #print 'packet.udpType', packet.udpType
            if packet.udpType in (UDP_TYPE_RTP, UDP_TYPE_RTP_EVENT):
                # This is a RTP packet including 2833 type
                tempData = packet.data
                if packet.udpType==UDP_TYPE_RTP_EVENT:
                    tempData = setTelephoneEventPt(tempData, self.telephoneEventPt)

                #print 'send RTP'
                self.rtpTransport.sendto(tempData, (callParameters.destination, self.sessionDestinationPort))

                if packet.udpType==UDP_TYPE_RTP_EVENT:
                    # RTP with same timestamp is duplicated message
                    if packet.rtpTimestamp!=self.cachedRtpTimestampFor2833:
                        tempDtmf = 'DTMF '+getDtmfChar(packet.dtmf)
                        self.__drawCallFlow(LEFT_TO_RIGHT, tempDtmf)
                        self.cachedRtpTimestampFor2833 = packet.rtpTimestamp

                self.packetIndex += 1
                time.sleep(TIME_ONE_TICK)
                continue
            elif packet.udpType==UDP_TYPE_SIP and packet.sipType==SIP_TYPE_BYE:
                self.__sendByeByPacket(packet.data)
                self.sipState = SIP_STATE_BYEING

                self.packetIndex += 1
                continue
            #else:
            #    continue


    def __moveCaseDialogTo(self, caseIndex=0, dialogIndex=0):
        """
        [Function]
        Move the channel's case to the indicated position,
        this function will load the cache file if the caseIndex move to the new postion

        [Argument]
        caseIndex: move to which case
        dialogIndex: move to which dialog

        [Return]
        return True if successfully, otherwise return False
        """

        if caseIndex<0:
            LOG.a('case index should not less then 0')

        if caseIndex>len(self.caseList)-1 and callParameters.isStressTest==False:
            print
            print 'All test cases are completed, please press Ctrl+C to exit.'
            return False
        # else:

        tempReleasingCacheName = ''
        try:
            if self.caseIndex>0:
                tempReleasingCacheName = self.caseList[self.caseIndex].cacheName
        except:
            pass

        try:
            if caseIndex>len(self.caseList)-1:
                # it is the last case, so go back to the first case
                if self.caseIndex==0:
                    # means there is only one case
                    self.caseIndex = 0
                    self.dialogIndex = 0
                    self.packetIndex = 0
                    self.nextInviteInSameCase = True
                    return True
                else:
                    # there is more than one cases
                    self.caseIndex = 0
                    self.dialogIndex = 0
                    self.packetIndex = 0

                    # it's not current using case, so need to get a new case
                    tempCaseData = self.caseList[self.caseIndex]
                    self.resourceQueue.put(QueueItem(ITEM_TYPE_GET_A_CASE_REQ, QueueItemData4Resource(self.channelQueue, tempCaseData.cacheName, tempReleasingCacheName)))
                    self.nextInviteInSameCase = False
                    return False
            else:
                if caseIndex==self.caseIndex:
                    if dialogIndex<=len(self.dialogPacketsList)-1:
                        # it is not the last dialog in the case
                        if self.dialogIndex!=dialogIndex:
                            self.dialogIndex = dialogIndex
                            self.packetIndex = 0
                        self.nextInviteInSameCase = True
                        return True
                    else:
                        # it is the last dialog in the case, so move to the next case
                        return self.__moveCaseDialogTo(self.caseIndex+1)
                else:
                    tempCaseData = self.caseList[caseIndex]

                    # it's not current using case, so need to load the packets list from the cache file
                    self.resourceQueue.put(QueueItem(ITEM_TYPE_GET_A_CASE_REQ, QueueItemData4Resource(self.channelQueue, tempCaseData.cacheName, tempReleasingCacheName)))
                    self.caseIndex = caseIndex
                    # the dialogIndex is resetted to 0
                    self.dialogIndex = 0
                    self.packetIndex = 0
                    self.nextInviteInSameCase = False
                    return False
        finally:
            self.__resetDialogContext()


    def __resetDialogContext(self):
        """
        [Function]
        reset something when begining a dialog

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        self.passed = True
        self.cachedRtpTimestamp = -1
        self.cachedIvrEventStr = ''
        self.ignoredIvrEventCount = 0


    def __restBeforeNextDialog(self, timeToRest):
        """
        [Function]
        Rest some time and clear the queue before start the next dialog

        [Argument]
        timeToRest: how long to rest

        [Return]
        (N/A)
        """

        time.sleep(timeToRest)
        self.channelQueue.put(QueueItem(ITEM_TYPE_HAVE_A_REST))

        while True:
            tempItem = self.channelQueue.get()

            if tempItem.itemType==ITEM_TYPE_SIGN_TO_KILL_THREAD:
                self.channelQueue.put(QueueItem(ITEM_TYPE_SIGN_TO_KILL_THREAD))
                return
            elif tempItem.itemType==ITEM_TYPE_HAVE_A_REST:
                return


    def __startDialog(self, caseIndex=0, dialogIndex=0):
        """
        [Function]
        Start dialog for the channel's case

        [Argument]
        caseIndex: which case
        dialogIndex: which dialog

        [Return]
        (N/A)
        """

        if self.__moveCaseDialogTo(caseIndex, dialogIndex):
            self.__sendInvite()


    def __sendInvite(self):
        """
        [Function]
        Start dialog by sending SIP Invite message

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        if self.sipState!=SIP_STATE_IDLE:
            LOG.e('the channel is in invalid status %d, when tring to send INVITE' % (self.sipState))
            return

        #print 'state: idle'

        tempCalled = ''
        tempRedirect = ''
        data = ''
        tempSIP = ''
        tempSDP = ''

        # get a case from the cases list
        tempCaseData = self.caseList[self.caseIndex]

        #LOG.writeLog('caseIndex: ' + str(self.caseIndex))
        #LOG.writeLog('dialogIndex: ' + str(self.dialogIndex))
        #LOG.writeLog('packetIndex: ' + str(self.packetIndex))
        #LOG.writeLog('snoopFileName: ' + str(tempCaseData.snoopFileName))

        # search the indicated dialog in the case
        foundTheDialog = False
        invitePackage = ''

        for packet in self.dialogPacketsList[self.dialogIndex]:
            # get the INVITE packet from the packets list at first
            #   1. this packet is a SIP INVITE
            #   2. the INVITE is for the indicated dialog
            if packet.udpType==UDP_TYPE_SIP and packet.sipType==SIP_TYPE_INVITE:
                foundTheDialog = True

                if not self.nextInviteInSameCase:
                    # prepare called
                    if callParameters.calledCount<=1:
                        if tempCaseData.caseConfig and len(tempCaseData.caseConfig.called)>0:
                            # use case config's CALLED number
                            tempCalled = tempCaseData.caseConfig.calledPrefix + tempCaseData.caseConfig.called
                        else:
                            # use callParameters' CALLED number
                            tempCalled = callParameters.calledPrefix + callParameters.called
                    else:
                        if self.calledIndex>self.maxCalledIndex:
                            self.calledIndex = self.minCalledIndex
                        if tempCaseData.caseConfig and len(tempCaseData.caseConfig.called)>0:
                            # use case config's CALLED number
                            tempCalled = tempCaseData.caseConfig.calledPrefix + tempCaseData.caseConfig.called
                        else:
                            # use callParameters' CALLED number
                            tempCalled = callParameters.calledPrefix + str(int(callParameters.called)+self.calledIndex)
                        self.calledIndex += 1
                    # save called to channel data
                    self.called = tempCalled

                    #LOG.writeLog('channel: %d, called: %s' % (self.channelIndex, self.called))

                    # prepare redirect & reason
                    tempDoRedirect = (callParameters.redirectCount>0)
                    if callParameters.redirectCount<=1:
                        if tempCaseData.caseConfig and len(tempCaseData.caseConfig.redirect)>0:
                            # use case config's REDIRECT number
                            tempDoRedirect = True
                            tempRedirect = tempCaseData.caseConfig.calledPrefix + tempCaseData.caseConfig.redirect

                            if len(tempCaseData.caseConfig.reason)>0:
                                # use case config's REASON number
                                tempReason = tempCaseData.caseConfig.reason
                            else:
                                # use default REASON number
                                tempReason = DEFAULT_PARAMETER_REASON
                        else:
                            # use callParameters' REDIRECT number & REASON
                            tempRedirect = callParameters.calledPrefix + callParameters.redirect
                            tempReason = callParameters.reason
                    else:
                        if self.redirectIndex>self.maxRedirectIndex:
                            self.redirectIndex = self.minRedirectIndex
                        if tempCaseData.caseConfig and len(tempCaseData.caseConfig.redirect)>0:
                            # use case config's REDIRECT number
                            tempRedirect = tempCaseData.caseConfig.calledPrefix + tempCaseData.caseConfig.redirect

                            if len(tempCaseData.caseConfig.reason)>0:
                                # use case config's REASON
                                tempReason = tempCaseData.caseConfig.reason
                            else:
                                # use default REASON
                                tempReason = DEFAULT_PARAMETER_REASON
                        else:
                            # use callParameters' REDIRECT number & REASON
                            tempRedirect = callParameters.calledPrefix + str(int(callParameters.redirect)+self.redirectIndex)
                            tempReason = callParameters.reason
                        self.redirectIndex += 1

                        #print 'redirectIndex:', self.redirectIndex
                    if tempDoRedirect:
                        # save redirect & reason to channel data
                        self.redirect = tempRedirect
                        self.reason = tempReason
                    else:
                        # clear redirect & reason
                        tempRedirect = ''
                        tempReason = ''
                        self.redirect = ''
                        self.reason = ''

                    # prepare calling
                    if tempCaseData.caseConfig and len(tempCaseData.caseConfig.calling)>0:
                        # use case config's CALLING number
                        tempCalling = tempCaseData.caseConfig.calling
                    else:
                        # use callParameters' CALLING number
                        tempCalling = callParameters.calling
                    # save calling to channel data
                    self.calling = tempCalling

                # create from tag
                tempFromTag = self.__createVoicebirdTag()
                self.fromTag = tempFromTag
                # create call ID
                self.callId = self.fromTag #+ '@' + callParameters.source

                data = packet.data.replace('\r\n', '\n').replace('\n', '\r\n')
                tempSIP,tempSDP = getSipSdp(data)

                if len(self.redirect)>0:
                    tempSIP += '\r\n' + 'Diversion: <sip:%s@%s:%d>;reason="%s";counter=1' % \
                                (self.redirect, callParameters.source, DEFAULT_SIP_PORT, self.reason)

                tempSDP = tempSDP.replace('[SOURCE]', callParameters.source)
                tempSDP = tempSDP.replace('[AUDIO_PORT]', str(self.rtpTransport.getsockname()[1]))
                tempSDP = tempSDP.strip() + '\r\n'
                tempSdpLen = len(tempSDP)

                tempSIP = tempSIP.replace('[DESTINATION]', callParameters.destination) \
                                 .replace('[CALLED]', self.called) \
                                 .replace('[SOURCE]', callParameters.source) \
                                 .replace('[FROM_TAG]', self.fromTag) \
                                 .replace('[LENGTH]', str(tempSdpLen))

                tempSIP = self.__processSip4PAI(tempSIP)
                invitePackage = tempSIP+'\r\n\r\n'+tempSDP

                self.__sendSip(invitePackage)
                self.sipState = SIP_STATE_WAITING_200
                LOG.writeLog('Send INVITE whose from tag is '+self.fromTag)
                #print 'state: waiting 200'

                tempCaseInfo = 'CASE (%d/%d): %s, DIALOG: %d/%d' % \
                                (self.caseIndex+1, len(self.caseList), tempCaseData.snoopFileName, self.dialogIndex+1, len(self.dialogPacketsList))
                tempCallerCalled = self.calling + self.called.rjust(PRINT_CENTER_WIDTH)
                self.__drawCallFlowHeader(tempCaseInfo, tempCallerCalled)
                self.__drawCallFlow(LEFT_TO_RIGHT, 'INVITE')

                # don't break, go on to find the ACK
                continue

            # if it is a ACK packet for this dialog, just save it for future using
            #   1. need to search ACK for this dialog
            #   2. in the same dialog
            #   3. it is a SIP ACK
            if foundTheDialog and packet.udpType==UDP_TYPE_SIP \
                              and packet.sipType==SIP_TYPE_ACK:
                self.ack = packet.data
                #print 'GET ACK:'
                #print packet.data

                # as soon as geting the ACK, break the dialog search
                break

        # if cannot find any dialog in the case, just move to the next case
        if not foundTheDialog:
            if self.dialogIndex<=0:
                LOG.a("There is no SIP INVITE found in the case '%s'" % (tempCaseData.snoopFileName))
                if len(self.caseList)==1:
                    raise
            self.__startDialog(self.caseIndex+1)


    def __processSip4PAI(self, sipStr):
        """
        [Function]
        Process SIP content for P-Asserted-Identity

        [Argument]
        SIP content string

        [Return]
        return processed SIP content
        """

        tempSIP = sipStr.strip()
        # PARAMETER -pai: P-Asserted-Identity
        if '-pai' in sys.argv:
            # replace calling number to be anonymous
            tempSIP = tempSIP.replace('[CALLING]', 'Anonymous')
            tempSIP = tempSIP.replace('[FROM_CALLING]', 'Anonymous')
            
            # replace From display name to be anonymous
            tempSIP = tempSIP.replace('[FROM_DISPLAY]', '"Anonymous"')

            tempSIP.strip()
            tempSipList = tempSIP.split('\r\n')

            # Note: Don't delete Contact field even P-Asserted-Identity
            #
            #tempNewSipList = []
            #
            # delete Contact
            #for line in tempSipList:
            #    if not line.startswith('Contact:'):
            #        tempNewSipList.append(line)

            # add two head fields
            tempSipList.append('P-Asserted-Identity: "%s"<sip:%s@%s>' % (self.calling, self.calling, callParameters.source))
            tempSipList.append('Privacy: id')
            tempSIP = '\r\n'.join(tempSipList).strip()   # Note: there is no \r\n in the end
        else:
            tempSIP = tempSIP.replace('[CALLING]', self.calling)
            tempSIP = tempSIP.replace('[FROM_CALLING]', self.calling)

        # PARAMETER -fdn: From Display Name
        if '-fdn' in sys.argv:
            strDisplayName = '"%s"' % (sys.argv[sys.argv.index('-fdn')+1])
            tempSIP = tempSIP.replace('[FROM_DISPLAY]', '"'+strDisplayName+'"')
        # PARAMETER -cfdn: Clear From Display Name
        elif '-cfdn' in sys.argv:
            tempSIP = tempSIP.replace('[FROM_DISPLAY]', '')
        else:
        	strDisplayName = '"%s"' % (self.calling)
        	tempSIP = tempSIP.replace('[FROM_DISPLAY]', '"'+strDisplayName+'"')

        #print tempSIP
        #print '-'*40

        return tempSIP


    def __createVoicebirdTag(self):
        """
        [Function]
        Create voicebird format (From) Tag

        [Argument]
        (N/A)

        [Return]
        return voicebird format tag
        """

        tempTag = VOICEBIRD_TAG_PREFIX
        tempTag += 'F' + str(self.channelIndex).zfill(LEN_OF_VOICEBIRD_TAG_UNIT)
        tempTag += 'C' + str(self.caseIndex).zfill(LEN_OF_VOICEBIRD_TAG_UNIT)
        tempTag += 'D' + str(self.dialogIndex).zfill(LEN_OF_VOICEBIRD_TAG_UNIT)
        tempTag += 'A' + str(int(time.time()*1000))
        return tempTag


    def __receive100(self, data, fromTag, callId):
        """
        [Function]
        Receive 100, and then only print information

        [Argument]
        data: SIP message data
        fromTag: From Tag
        callId: Call-ID

        [Return]
        If this message is SIP response 100 for this dialog, return True. Otherwise return False
        """

        reResponse = RE_SIP_100.search(data)
        if reResponse:
            if fromTag==self.fromTag and callId==self.callId:
                self.__drawCallFlow(RIGHT_TO_LEFT, '100 Trying')
                if data.find(IVR_8250_SIGN)>-1:
                    self.is8250 = True
                return True
            else:
                LOG.w("The 100 can not match. Waiting From tag '%s', Call-ID '%s', but received From tag '%s', Call-ID '%s'" % (self.fromTag, self.callId, fromTag, callId))

        #print data
        #print '-'*70
        return False


    def __receive180(self, data, fromTag, callId):
        """
        [Function]
        Receive 180, and then only print information

        [Argument]
        data: SIP message data
        fromTag: From Tag
        callId: Call-ID

        [Return]
        If this message is SIP response 180 for this dialog, return True. Otherwise return False
        """

        reResponse = RE_SIP_180.search(data)
        if reResponse:
            if fromTag==self.fromTag and callId==self.callId:
                self.__drawCallFlow(RIGHT_TO_LEFT, '180 Ring')
                return True
            else:
                LOG.w("The 180 can not match. Waiting From tag '%s', Call-ID '%s', but received From tag '%s', Call-ID '%s'" % (self.fromTag, self.callId, fromTag, callId))

        #print data
        #print '-'*70
        return False


    def __receive183(self, data, fromTag, callId):
        """
        [Function]
        Receive 183

        [Argument]
        data: SIP message data
        fromTag: From Tag
        callId: Call-ID

        [Return]
        If this message is SIP response 183 for this dialog, return True. Otherwise return False
        """

        reResponse = RE_SIP_183.search(data)
        if reResponse:
            if fromTag==self.fromTag and callId==self.callId:
                self.__drawCallFlow(RIGHT_TO_LEFT, '183 Session Progress')
                return True
            else:
                LOG.w("The 183 can not match. Waiting From tag '%s', Call-ID '%s', but received From tag '%s', Call-ID '%s'" % (self.fromTag, self.callId, fromTag, callId))
                return False

        #print data
        #print '-'*70
        return False


    def __receiveErrorResponse(self, data, fromTag, callId):
        """
        [Function]
        Receive error response

        [Argument]
        data: SIP message data
        fromTag: From Tag
        callId: Call-ID

        [Return]
        (isThisMsgErrorResponse, inThisDialog)
        """

        reResponse = RE_SIP_RESPONSE.search(data)
        if reResponse:
            if fromTag==self.fromTag and callId==self.callId:
                self.toTag = getToTag(data)
                tempResponseCode = getResponseCode(data)
                self.__drawCallFlow(RIGHT_TO_LEFT, tempResponseCode)
                return (True, True)
            else:
                tempLogStr = """
-- This error response cannot match its dialog --
+Channel Information:
 From Tag: %s
 To Tag: %s
 Call-ID: %s
+Error Response Message:
%s
""" % (self.fromTag, self.toTag, self.callId, data)
                LOG.w(tempLogStr)
                return (True, False)
        else:
            return (False, False)


    def __receive200(self, data, fromTag, callId):
        """
        [Function]
        Receive 200

        [Argument]
        data: SIP message data
        fromTag: From Tag
        callId: Call-ID

        [Return]
        If this message is SIP response 200 for this dialog, return True. Otherwise return False
        """

        #print '200 OK data:'
        #print data

        reResponse = RE_SIP_200.search(data)
        if reResponse:
            if self.sipState==SIP_STATE_BYEING:
                if fromTag==self.fromTag and callId==self.callId:
                    #self.__drawCallFlow(RIGHT_TO_LEFT, '200 OK')
                    return True
                else:
                    LOG.w("The 200 can not match. Waiting From tag '%s', Call-ID '%s', but received From tag '%s', Call-ID '%s'" % (self.fromTag, self.callId, fromTag, callId))
                    return False
            else:
                try:
                    # PARAMETER -w: Wait time, how long to wait after 183/200 then send RTP
                    tempWaitTimeThenRtp = int(sys.argv[sys.argv.index('-w')+1])
                    self.baseTimeForRtp = time.time() + tempWaitTimeThenRtp
                except:
                    self.baseTimeForRtp = time.time()

                if fromTag==self.fromTag and callId==self.callId:
                    self.__drawCallFlow(RIGHT_TO_LEFT, '200 OK')
                    self.toTag = getToTag(data)
                    self.sessionDestinationPort = getSdpMediaPort(data)
                    self.telephoneEventPt = getTelephoneEventPtFromSdp(data)
                    LOG.startADialog()
                    return True
                else:
                    LOG.w("The 200 can not match. Waiting From tag '%s', Call-ID '%s', but received From tag '%s', Call-ID '%s'" % (self.fromTag, self.callId, fromTag, callId))
                    return False

        return False


    def __receiveBye(self, data, fromTag, callId):
        """
        [Function]
        Receive Bye, then create the Ack message data

        [Argument]
        data: SIP message data
        fromTag: From Tag
        callId: Call-ID

        [Return]
        (isThisMsgBye, inThisDialog, byeResponse)
        """

        reBye = RE_SIP_BYE.search(data)
        if reBye:
            tempToTag = getToTag(data)

            if fromTag==self.toTag and tempToTag==self.fromTag and callId==self.callId:
                tempViasList = getViasList(data)
                tempVias = '\r\n'.join(tempViasList).strip()

                tempCallIdStr = getCallIdStr(data).strip()
                tempCSeqStr = getCSeqStr(data).strip()
                tempFromStr = getFromStr(data).strip()
                tempToStr = getToStr(data).strip()

                tempByeResponse = 'SIP/2.0 200 OK\r\n'
                tempByeResponse += tempVias + '\r\n'
                tempByeResponse += tempToStr + '\r\n'
                tempByeResponse += tempFromStr + '\r\n'
                tempByeResponse += tempCallIdStr + '\r\n'
                tempByeResponse += tempCSeqStr + '\r\n'
                tempByeResponse += 'Content-Length:0\r\n\r\n'
                #print 'Bye ACK:'
                #print tempByeResponse

                self.__drawCallFlow(RIGHT_TO_LEFT, 'BYE')
                LOG.writeLog('Receive BYE whose from tag is %s, to tag is %s' % (fromTag, tempToTag))
                return (True, True, tempByeResponse)
            else:
                tempLogStr = """
-- This BYE cannot match its dialog --
+Received
 From Tag: %s
 To Tag: %s
 Call-ID: %s
+Channel's
 To Tag: %s
 From Tag: %s
 Call-ID: %s
""" % (fromTag, tempToTag, callId, self.toTag, self.fromTag, self.callId)
                LOG.w(tempLogStr)
                return (True, False, None)
        else:
            return (False, False, None)


    def __sendSip(self, data):
        """
        [Function]
        Send SIP message

        [Argument]
        data: message data

        [Return]
        (N/A)
        """
        self.sipTransport.send(data)


    def __sendAck(self):
        """
        [Function]
        Send Ack after receiveing 200

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        if len(self.ack)<4:
            LOG.a('ACK is not ready, please check your test case')
            return

        tempSIP = self.ack.replace('\r\n', '\n').replace('\n', '\r\n')
        tempSIP = tempSIP.replace('[DESTINATION]', callParameters.destination) \
                         .replace('[CALLED]', self.called) \
                         .replace('[SOURCE]', callParameters.source) \
                         .replace('[FROM_TAG]', self.fromTag) \
                         .replace('[TO_TAG]', self.toTag) \
                         .replace('[REDIRECT]', self.redirect) \
                         .replace('[REASON]', self.reason)

        tempSIP = self.__processSip4PAI(tempSIP)
        self.__sendSip(tempSIP+'\r\n\r\n')
        self.__drawCallFlow(LEFT_TO_RIGHT, 'ACK')


    def __sendByeByPacket(self, packetData):
        """
        [Function]
        Send BYE according to the packet data

        [Argument]
        packetData: packet data

        [Return]
        (N/A)
        """

        tempSIP = packetData.replace('\r\n', '\n').replace('\n', '\r\n')
        tempSIP = tempSIP.replace('[DESTINATION]', callParameters.destination) \
                         .replace('[CALLED]', self.called) \
                         .replace('[SOURCE]', callParameters.source) \
                         .replace('[FROM_TAG]', self.fromTag) \
                         .replace('[TO_TAG]', self.toTag) \
                         .replace('[REDIRECT]', self.redirect) \
                         .replace('[REASON]', callParameters.reason)

        tempSIP = self.__processSip4PAI(tempSIP)
        self.__sendSip(tempSIP+'\r\n\r\n')
        LOG.writeLog('Send BYE whose from tag is '+self.fromTag)
        self.__drawCallFlow(LEFT_TO_RIGHT, 'BYE')
        self.__drawCallFlowSummary()


    def __sayGoodBye(self):
        """
        [Function]
        Send BYE according to the template
        Note: this function only used when exit

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        templateBye = TEMPLATE_BYE.strip().replace('\n', '\r\n')
        tempSIP = templateBye.replace('[DESTINATION]', callParameters.destination) \
                             .replace('[CALLED]', self.called) \
                             .replace('[SOURCE]', callParameters.source) \
                             .replace('[FROM_TAG]', self.fromTag) \
                             .replace('[TO_TAG]', self.toTag) \
                             .replace('[REDIRECT]', self.redirect) \
                             .replace('[REASON]', self.reason)

        tempSIP = self.__processSip4PAI(tempSIP)
        self.__sendSip(tempSIP+'\r\n\r\n')
        self.__drawCallFlow(LEFT_TO_RIGHT, 'BYE')
        self.__drawCallFlowSummary(RESULT_VALUE_INTERRUPTED)


    def __sendByeResponse(self, byeResponse):
        """
        [Function]
        Response the Bye when called side hands up

        [Argument]
        byeResponse: the ACK data for response Bye

        [Return]
        (N/A)
        """

        self.__sendSip(byeResponse)
        self.__drawCallFlow(LEFT_TO_RIGHT, '200 OK')


    def __receiveSip(self, data):
        """
        [Function]
        used to receive SIP message and manage the SIP state

        [Argument]
        data: the data received

        [Return]
        return True if it is a SIP message (then stop to dealing with the behind packets in list), otherwise return False
        """

        #print data
        #print '-'*70

        tempFromTag = getFromTag(data)
        tempCallId = getCallId(data)

        # BYE from destination
        tempIsMsgBye,tempInTheSameDialog,tempByeResponse = self.__receiveBye(data, tempFromTag, tempCallId)
        if tempIsMsgBye:
            if tempInTheSameDialog:
                self.__sendByeResponse(tempByeResponse)
                self.sipState = SIP_STATE_BYED

                if self.__gotoNextIvrEvent():
                    tempPacket = self.dialogPacketsList[self.dialogIndex][self.packetIndex]
                    if tempPacket.udpType==UDP_TYPE_SIP and tempPacket.sipType==SIP_TYPE_BYE:
                        #self.passed &= True
                        self.__drawCallFlowSummary()
                    else:
                        if self.passed:
                            self.__drawCallFlowSummary(RESULT_VALUE_PASS_BUT_UNCOMPLETED)
                        else:
                            self.passed &= False
                            self.__drawCallFlowSummary()
                else:
                    if self.passed:
                        tempResultValue = RESULT_VALUE_PASS_BUT_DEFECTIVE_CASE
                    else:
                        tempResultValue = RESULT_VALUE_FAIL
                    self.__drawCallFlowSummary(tempResultValue)
                self.__restBeforeNextDialog(TIME_ONE_WINK)
                self.__startDialog(self.caseIndex, self.dialogIndex+1)
            return True
        #else:

        if self.__receive100(data, tempFromTag, tempCallId):
            return True

        if self.__receive180(data, tempFromTag, tempCallId):
            return True

        if self.__receive183(data, tempFromTag, tempCallId):
            return True

        if self.__receive200(data, tempFromTag, tempCallId):
            if self.sipState==SIP_STATE_WAITING_200:
                self.__sendAck()
                self.sipState = SIP_STATE_AFTER_ACK
                #print 'state: after ack'
            elif self.sipState==SIP_STATE_BYEING:
                self.sipState = SIP_STATE_BYED

                self.__restBeforeNextDialog(TIME_ONE_WINK*3)
                self.__startDialog(self.caseIndex, self.dialogIndex+1)
            else:
                LOG.i('receive 200 OK in invalid SIP status %d'  % (self.sipState))
            return True

        tempIsErrorResponse,tempInTheSameDialog = self.__receiveErrorResponse(data, tempFromTag, tempCallId)
        if tempIsErrorResponse:
            if tempInTheSameDialog:
                self.__sendAck()
                self.sipState = SIP_STATE_BYED

                self.passed &= False
                self.__drawCallFlowSummary(RESULT_VALUE_SIP_ERROR)
                self.__startDialog(self.caseIndex, self.dialogIndex+1)
            return True

        return False


class Parameters:
    """
    [Class]
    This is a struct used to dump the parameters to a file
    """

    destination = ''
    calledPrefix = ''
    calledCount = 1
    called = ''
    source = ''
    calling = ''
    redirectCount = 0
    redirect = ''
    reason = ''
    isStressTest = False
    channelCount = 1

    def __str__(self):
        tempStr = ''
        tempStr += ' destination: ' + self.destination + '\n'
        tempStr += ' calledPrefix: ' + self.calledPrefix + '\n'
        tempStr += ' calledCount: ' + str(self.calledCount) + '\n'
        tempStr += ' called: ' + self.called + '\n'
        tempStr += ' source: ' + self.source + '\n'
        tempStr += ' calling: ' + self.calling + '\n'
        tempStr += ' redirectCount: ' + str(self.redirectCount) + '\n'
        tempStr += ' redirect: ' + self.redirect + '\n'
        tempStr += ' reason: ' + self.reason + '\n'
        tempStr += ' isStressTest: ' + str(self.isStressTest) + '\n'
        tempStr += ' channelCount: ' + str(self.channelCount)
        return tempStr


class CaseConfig:
    """
    [Class]
    This is a struct used to save Case Configuration
    """

    calledPrefix = ''
    called = ''
    calling = ''
    redirect = ''
    reason = ''

    def __str__(self):
        tempStr = ''
        tempStr += ' calledPrefix: ' + self.calledPrefix + '\n'
        tempStr += ' called: ' + self.called + '\n'
        tempStr += ' calling: ' + self.calling + '\n'
        tempStr += ' redirect: ' + self.redirect + '\n'
        tempStr += ' reason: ' + self.reason
        return tempStr


class Distributor:
    """
    [Class]
    Used to receive SIP/RTP messages and then distributor messages to ChannelWorker
    """

    channelQueueList = []           # value: ChannelQueue
    channelQueueDictByUdpPort = {}  # key: UDP port, value: ChannelQueue
                                    # channelQueueDictByUdpPort is used to match the received RTP message to the channel according to the RTP message's IP port
    resourceQueue = None

    def __init__(self, caseList):
        """
        [Function]
        new a Distributor object

        [Argument]
        caseList: list of CaseData
        """

        self.caseList = caseList
        try:
            callParameters.destination = socket.gethostbyname(callParameters.destination)
        except:
            LOG.a('The destination host address is invalid, please try to setup the call parameter again')
            sys.exit(1)
            return

        if callParameters.calling=='':
            callParameters.calling = DEFAULT_PARAMETER_PHONE

        if callParameters.redirect=='':
            callParameters.redirect = callParameters.called

        if callParameters.reason=='':
            callParameters.reason = DEFAULT_PARAMETER_REASON

        self.sipTransport = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            self.sipTransport.bind(('', DEFAULT_SIP_PORT))
        except:
            print 'The SIP port %d has been used by another program, please confirm and try again later.' % (DEFAULT_SIP_PORT)
            sys.exit(1)
            return

        # it's very important to setsockopt
        self.sipTransport.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sipTransport.connect((callParameters.destination, DEFAULT_SIP_PORT))

        self.readableChannels = [self.sipTransport,]

        self.resourceQueue = Queue.Queue()
        tempResourceController = ResourceController(self.resourceQueue)
        tempResourceController.setDaemon(True)
        tempResourceController.start()

        for channelIndex in range(callParameters.channelCount):
            # create Queue object
            tempChannelQueue = Queue.Queue()

            # create ChannelWorker object, which is a thread
            tempChannelWorker = ChannelWorker(channelIndex, self.caseList, self.sipTransport, tempChannelQueue, self.resourceQueue)
            tempRtpTransport = tempChannelWorker.getLocalRtpTransport()

            # add to the calls list
            self.channelQueueList.append(tempChannelQueue)

            self.readableChannels.append(tempRtpTransport)
            self.channelQueueDictByUdpPort[tempRtpTransport.getsockname()[1]] = tempChannelQueue

            # start ChannelWorker
            tempChannelWorker.setDaemon(True)
            tempChannelWorker.start()


    def __del__(self):
        """
        [Function]
        Kill all threads in this function

        [Argument]
        (N/A)
        """

        # Bye all
        for tempChannelQueue in self.channelQueueList:
            # Stop ChannelWorker thread
            tempChannelQueue.put(QueueItem(ITEM_TYPE_SIGN_TO_KILL_THREAD))

        if self.resourceQueue:
            self.resourceQueue.put(QueueItem(ITEM_TYPE_SIGN_TO_KILL_THREAD))

        # give some time to stop threads
        timeToExit = TIME_ONE_WINK*len(self.channelQueueList)*5
        print
        print 'Wait a minute to exit ...'

        if timeToExit > MAX_TIME_TO_EXIT:
            timeToExit = MAX_TIME_TO_EXIT

        if timeToExit < MIN_TIME_TO_EXIT:
            timeToExit = MIN_TIME_TO_EXIT

        time.sleep(timeToExit)
        deleteLogObj()
        time.sleep(TIME_ONE_WINK*3)


    def doSelect(self):
        """
        [Function]
        distribute messages to ChannelWorker

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        if callParameters.isStressTest or 'nf' in sys.argv:
            # Note: the line count of this information is used by __printStatisticInScreen
            print 'Wait to start ...'
            print

        for channelQueue in self.channelQueueList:
            # give a sign to ChannelWorker to start dialog
            channelQueue.put(QueueItem(ITEM_TYPE_START_WORK))

        while True:
            Rs, Ws, Es = select.select(self.readableChannels, [], [], TIME_ONE_WINK)
            if len(Rs)>0:
                for readable in Rs:
                    if readable!=self.sipTransport:
                        # 1. deal with RTP message before SIP
                        try:
                            tempData = readable.recv(MIN_UDP_LEN)
                        except KeyboardInterrupt:
                            raise KeyboardInterrupt
                        except:
                            LOG.w('Cannot receive the RTP data')
                        else:
                            #if tempData.startswith('BYE'):
                            #    print 'receive BYE:\n%s' % (tempData)

                            #print 'receive RTP'
                            tempPayloadType = quicklyGetPt(tempData)

                            if tempPayloadType not in (PAYLOAD_TYPE_IVR_RECORD_FILE, PAYLOAD_TYPE_IVR_PROMPT):
                                #LOG.i('A RTP package with pt %d is ignored' % (tempPayloadType))
                                continue
                            #else:

                            tempPort = readable.getsockname()[1]
                            tempChannelQueue = self.channelQueueDictByUdpPort[tempPort]
                            if not tempChannelQueue:
                                LOG.w('Cannot find the rtp queue according to the UDP port %d' % (tempPort))
                            else:
                                tempChannelQueue.put(QueueItem(ITEM_TYPE_RTP_DATA, tempData))
                    else:
                        # 2. deal with SIP message
                        try:
                            tempData = self.sipTransport.recv(MIN_UDP_LEN*2)
                        except KeyboardInterrupt:
                            raise KeyboardInterrupt
                        except:
                            LOG.w('Cannot receive the SIP data')
                        else:
                            #print 'receive SIP:\n', tempData
                            self.__distributeSipMsg(tempData)


    def __distributeSipMsg(self, data):
        """
        [Function]
        Distribute SIP message to ChannelWorker

        [Argument]
        data: the received data

        [Return]
        return True if it is distributed successfully, otherwise return False
        """

        try:
            tempVoicebirdTagPrefixPos = data.index(VOICEBIRD_TAG_PREFIX)
            tempChannelIndex = int(data[tempVoicebirdTagPrefixPos+LEN_OF_VOICEBIRD_TAG_PREFIX+1 : tempVoicebirdTagPrefixPos+LEN_OF_VOICEBIRD_TAG_PREFIX+1+LEN_OF_VOICEBIRD_TAG_UNIT])
        except KeyboardInterrupt:
            raise KeyboardInterrupt
        except:
            return False

        if tempChannelIndex<len(self.channelQueueList):
            self.channelQueueList[tempChannelIndex].put(QueueItem(ITEM_TYPE_SIP_DATA, data))
            return True
        else:
            return False


class SnoopParser:
    """
    [Class]
    Read snoop file(s) then create the packet list for later usage
    """

    # global in the object
    caseList = []
    packetsList = []        # in fact it's for template using to save all packets
    dialogPacketsList = []
    dialogIndex = -1        # Note: init it to be -1 not 0
    fileIndex = 0

    # global in every file, it is very useful to match to Ethreal's packet no.
    packetIndex = 0

    telephoneEventPtInSdp = -1

    dialogNumbers = []
    firstDialogCallingNumber = ''

    def __init__(self, files):
        """
        [Function]
        New a object of SnoopParser

        [Argument]
        files: a list parameter to carry snoop files
        """

        if len(files)<1:
            LOG.a('No snoop file')
            raise

        #print files

        fileName = ''
        for fileIndex in range(len(files)):
            fileName = files[fileIndex]
            tempDplFileName = caseNameToCacheName(fileName)+DIALOG_PACKETS_LIST_FILE_EXT

            # PARAMETER -fp: Force to Parser snoop file
            if '-fp' in sys.argv:
                LOG.writeLog("Force to parse the case '%s'" % (fileName))
            else:
                if os.path.exists(tempDplFileName):
                    tempCifVersion,tempOriginalFileCreateTime,tempOriginalFileSize = self.__getSnoopFileInfo(fileName)
                    if tempCifVersion!=CIF_VERSION:
                        LOG.writeLog("The case '%s' cache CIF version is %d" % (fileName, tempCifVersion))
                    elif tempOriginalFileCreateTime:
                        tempNewSnoopFileStatus = os.stat(fileName)
                        if tempOriginalFileCreateTime==tempNewSnoopFileStatus.st_ctime \
                                and tempOriginalFileSize==tempNewSnoopFileStatus.st_size:
                            LOG.writeLog("The case '%s' is unchanged" % (fileName))

                            # add the case to the list
                            tempCaseData = CaseData()
                            tempCaseData.snoopFileName = fileName
                            tempCaseData.cacheName = caseNameToCacheName(fileName)
                            tempCaseData.caseConfig = self.__getCaseConfig(fileName)
                            self.caseList.append(tempCaseData)

                            # PARAMETER -vp: View the Packet list, means to print the packet list's information
                            if '-vp' in sys.argv:
                                tempDialogPacketsList = loadDialogPacketsListFromCache(tempCaseData.cacheName)
                                self.__printDialogPacketsList(len(self.caseList)-1, fileName, tempDialogPacketsList)

                            continue
                        else:
                            LOG.writeLog("The case '%s' is changed" % (fileName))
                    else:
                        LOG.writeLog("New case '%s'" % (fileName))
                else:
                    LOG.writeLog("Find that the cache file '%s' has been removed by somebody" % (tempDplFileName))

            fileobj = file(fileName, 'rb')

            if not self.__checkFileHeader(fileobj):
                LOG.a("'%s' is NOT a snoop file, you may 'Save As' it to a snoop file by Ethreal (Wireshark)" % (fileName))
                if len(files)==1:
                    fileobj.close()
                    raise
            else:
                # PARAMETER -vf: View the File, means to print the snoop file's content
                if '-vf' in sys.argv:
                    print '-- file (%d) -- %s' % (fileIndex, fileName)

                self.packetIndex = 0    # init packet index to 0, for it's global in each file
                self.__readPackets(fileName, fileobj)

            fileobj.close()


    def getCaseList(self):
        """
        [Function]
        Get all test case data list

        [Argument]
        (N/A)

        [Return]
        Return a list of CaseData
        """
        return self.caseList


    def __printDialogPacketsList(self, caseIndex, snoopFileName, dialogPacketsList):
        """
        [Function]
        Print the DialogPacketsList

        [Argument]
        caseIndex: case index
        snoopFileName: snoop file name
        dialogPacketsList: dialog packets list

        [Return]
        (N/A)
        """

        dialogCount = len(dialogPacketsList)
        print '-- CASE %d, Snoop File: %s --' % (caseIndex, snoopFileName)
        print 'There is/are', dialogCount, 'dialog(s)'
        print

        for dialogIndex in range(dialogCount):
            packetIndex = 0
            for packet in dialogPacketsList[dialogIndex]:
                print '-'*50, 'CASE', caseIndex, '- dialog', dialogIndex, ', packet', packetIndex, '--'
                print str(packet)
                print
                packetIndex += 1


    def __getSnoopFileInfo(self, fileName):
        """
        [Function]
        get snoop file's information in CaseInformation

        [Argument]
        fileName:snoop file name

        [Return]
        (CaseInformation.cifVersion, CaseInformation.snoopFileCreateTime, CaseInformation.snoopFileSize)
        """

        caseInformation = loadCaseInfoFromCase(fileName)
        if caseInformation:
            return (caseInformation.cifVersion, caseInformation.snoopFileCreateTime, caseInformation.snoopFileSize)
        else:
            return (0, None, None)


    def __checkFileHeader(self, fileobj):
        """
        [Function]
        Check whether it is a snoop file

        [Argument]
        fileobj: file object of snoop file

        [Return]
        If it is a snoop file, return True. Otherwise return False

        [See Also]
        ########################################################
        # RFC 1761
        # http://www.faqs.org/rfcs/rfc1761.html
        ########################################################
        """

        tmpBuffer = fileobj.read(8+4+4)
        if not tmpBuffer:
            LOG.a('EOF in __checkFileHeader')
            raise
        iStart = 0
        iEnd = 0

        # 1. Identification Pattern: 8 octet
        iEnd = iStart+8
        identificationPattern = struct.unpack('B'*8, tmpBuffer[iStart:iEnd])
        if identificationPattern != SNOOP_IDENTIFICATION_PATTERN_SNOOP:
            return False
        if '-vf' in sys.argv:
            print 'Identification Pattern:', tuple2Hex(identificationPattern)
        iStart = iEnd

        # 2. Version Number: 4 octet
        iEnd = iStart+4
        versionNumber = struct.unpack('!I', tmpBuffer[iStart:iEnd])[0]
        if versionNumber != SNOOP_VERSION_NUMBER:
            return False
        if '-vf' in sys.argv:
            print 'Version Number:', versionNumber
        iStart = iEnd

        # 3. Datalink Type: 4 octet
        iEnd = iStart+4
        datalinkType = struct.unpack('!I', tmpBuffer[iStart:iEnd])[0]
        if datalinkType != SNOOP_DATALINK_TYPE_ETHERNET:
            return False
        if '-vf' in sys.argv:
            print 'Datalink Type:', datalinkType
        iStart = iEnd

        return True


    def __readPacketRecord(self, fileobj):
        """
        [Function]
        Read every packet record in the file

        [Argument]
        fileobj: file object of snoop file

        [Return]
        If EOF return False, otherwise return True

        [See Also]
        ########################################################
        # RFC 1761
        # http://www.faqs.org/rfcs/rfc1761.html
        ########################################################
        """

        # Packet Record format: as six 32-bit (4-octet) integer values
        PACKET_RECORD_HEADER_LEN = 6*4
        tmpBuffer = fileobj.read(PACKET_RECORD_HEADER_LEN)
        if not tmpBuffer:
            if '-vf' in sys.argv:
                print 'EOF in __readPacketRecord'
            return False

        iStart = 0
        iEnd = 0

        self.packetIndex += 1
        if '-vf' in sys.argv:
            print '-vf --', self.packetIndex, '-'*70

        # 1. Original Length: 4 octet
        iEnd = iStart+4
        originalLength = struct.unpack('!I', tmpBuffer[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Original Length:', originalLength
        iStart = iEnd

        # 2. Included Length: 4 octet
        iEnd = iStart+4
        includedLength = struct.unpack('!I', tmpBuffer[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Included Length:', includedLength
        iStart = iEnd

        # 3. Packet Record Length: 4 octet
        iEnd = iStart+4
        packetRecordLength = struct.unpack('!I', tmpBuffer[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Packet Record Length:', packetRecordLength
        iStart = iEnd

        # 4. Cumulative Drops: 4 octet
        iEnd = iStart+4
        cumulativeDrops = struct.unpack('!I', tmpBuffer[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Cumulative Drops:', cumulativeDrops
        iStart = iEnd

        # 5. Timestamp Seconds: 4 octet
        iEnd = iStart+4
        timestampSeconds = struct.unpack('!I', tmpBuffer[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Timestamp Seconds:', timestampSeconds
        iStart = iEnd

        # 6. Timestamp Microseconds: 4 octet
        iEnd = iStart+4
        timestampMicroseconds = struct.unpack('!I', tmpBuffer[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Timestamp Microseconds:', timestampMicroseconds
        iStart = iEnd

        # prepare UDP Packet
        self.dialogPacket = DialogPacket()
        #self.dialogPacket.fileName = os.path.split(filename)[1]
        self.dialogPacket.originalPacketIndex = self.packetIndex
        self.dialogPacket.timestamp = '%d.%06d' % (timestampSeconds, timestampMicroseconds)

        # 7. Packet Data
        packetDataLen = packetRecordLength-PACKET_RECORD_HEADER_LEN
        tmpBuffer = fileobj.read(packetDataLen)

        self.__readEthernetII(tmpBuffer)

        if '-vf' in sys.argv:
            print
        return True


    def __readEthernetII(self, ep):
        """
        [Function]
        Read packet's EthernetII head

        [Argument]
        ep: the EthernetII data

        [Return]
        (N/A)

        [See Also]
        ########################################################
        # http://www.firewall.cx/ethernet-frames-ethernet-ii.php
        ########################################################
        """

        if '-vf' in sys.argv:
            print '-- EthernetII --'

        iStart = 0
        iEnd = 0

        # 1. Destination: 6 octet
        iEnd = iStart+6
        destination = struct.unpack('B'*6, ep[iStart:iEnd])
        if '-vf' in sys.argv:
            print 'Destination:', tuple2Hex(destination)
        iStart = iEnd

        # 2. Source: 6 octet
        iEnd = iStart+6
        source = struct.unpack('B'*6, ep[iStart:iEnd])
        if '-vf' in sys.argv:
            print 'Source:', tuple2Hex(source)
        iStart = iEnd

        # 3. Type: 2 octet
        iEnd = iStart+2
        packetType = struct.unpack('!H', ep[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Type: 0x%04x' % (packetType)
        iStart = iEnd

        if packetType==ETHERNET_TYPE_IP:
            self.__readIp(ep[iStart:])
        else:
            if '-vf' in sys.argv:
                print 'NOT IP'


    def __readIp(self, ipp):
        """
        [Function]
        Read packet's IP head

        [Argument]
        ipp: IP packet data

        [Return]
        (N/A)

        [See Also]
        ########################################################
        # http://www.networksorcery.com/enp/protocol/ip.htm
        ########################################################
        """

        if '-vf' in sys.argv:
            print '-- IP (Internet Protocol) --'

        iFixIpHeaderLen = 0

        iStart = 0
        iEnd = 0

        # 1. Version: 4 bits
        # 2. Header Length: 4 bits
        # = 1 octet
        iFixIpHeaderLen += 1
        iEnd = iStart+1
        vhl = struct.unpack('B', ipp[iStart:iEnd])[0]
        version = vhl >> 4
        if '-vf' in sys.argv:
            print 'Version:', version

        headerLength = vhl & 0xf
        if '-vf' in sys.argv:
            print 'Header Length:', headerLength
        iStart = iEnd

        # 3. Type of Service: 1 octet
        iFixIpHeaderLen += 1
        iEnd = iStart+1
        typeOfService = struct.unpack('B', ipp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Type of Service:', typeOfService
        iStart = iEnd

        # 4. Total length: 2 octet
        iFixIpHeaderLen += 2
        iEnd = iStart+2
        totalLength = struct.unpack('!H', ipp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Total length:', totalLength
        iStart = iEnd

        # 5. Identification: 2 octet
        iFixIpHeaderLen += 2
        iEnd = iStart+2
        identification = struct.unpack('!H', ipp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Identification:', identification
        iStart = iEnd

        # 6. Flags: 3 bits
        # 7. Fragment Offset: 13 bits
        # = 2 octet
        iFixIpHeaderLen += 2
        iEnd = iStart+2
        ffo = struct.unpack('B'*2, ipp[iStart:iEnd])[0]

        flags = ffo >> 13
        if '-vf' in sys.argv:
            print 'Flags:', flags

        fragmentOffset = ffo & 0x1fff
        if '-vf' in sys.argv:
            print 'Fragment Offset:', fragmentOffset
        iStart = iEnd

        # 8. Time to Live: 1 octet
        iFixIpHeaderLen += 1
        iEnd = iStart+1
        ttl = struct.unpack('B', ipp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Time to Live:', ttl
        iStart = iEnd

        # 8. Protocol: 1 octet
        iFixIpHeaderLen += 1
        iEnd = iStart+1
        protocol = struct.unpack('B', ipp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Protocol:', protocol
        iStart = iEnd

        # 9. Header checksum: 2 octet
        iFixIpHeaderLen += 2
        iEnd = iStart+2
        headerChecksum = struct.unpack('!H', ipp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Header checksum: 0x%x' % (headerChecksum)
        iStart = iEnd

        # 10. Source IP address: 4 octet
        iFixIpHeaderLen += 4
        iEnd = iStart+4
        sourceIpAddress = struct.unpack('B'*4, ipp[iStart:iEnd])
        if '-vf' in sys.argv:
            print 'Source IP address:', sourceIpAddress
        iStart = iEnd

        # 11. Destination IP address: 4 octet
        iFixIpHeaderLen += 4
        iEnd = iStart+4
        destinationIpAddress = struct.unpack('B'*4, ipp[iStart:iEnd])
        if '-vf' in sys.argv:
            print 'Destination IP address:', destinationIpAddress
        iStart = iEnd

        # 12. Options
        iOptionsLen = int(headerLength)*4 - iFixIpHeaderLen
        if '-vf' in sys.argv:
            print 'Options Len:', iOptionsLen
        if iOptionsLen>0:
            iEnd = iStart+iOptionsLen
            options = struct.unpack('B'*iOptionsLen, ipp[iStart:iEnd])
            if '-vf' in sys.argv:
                print 'Options:', options
            iStart = iEnd

        if protocol!=IP_PROTOCOL_UDP:
            if '-vf' in sys.argv:
                print 'NOT UDP'
        else:
            # prepare UDP Packet
            self.dialogPacket.sourceIp = '%s.%s.%s.%s' % (sourceIpAddress[:])
            self.dialogPacket.destinationIp = '%s.%s.%s.%s' % (destinationIpAddress[:])
            self.__readUdp(ipp[iStart:])


    def __readUdp(self, udp):
        """
        [Function]
        Read packet's UDP head

        [Argument]
        upd: UDP packet data

        [Return]
        (N/A)

        [See Also]
        ########################################################
        # http://www.networksorcery.com/enp/protocol/udp.htm
        ########################################################
        """

        if '-vf' in sys.argv:
            print '-- UDP (User Datagram Protocol) --'

        iStart = 0
        iEnd = 0

        # 1. Source Port: 2 octet
        iEnd = iStart+2
        sourcePort = struct.unpack('!H', udp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Source Port:', sourcePort
        iStart = iEnd

        # 2. Destination Port: 2 octet
        iEnd = iStart+2
        destinationPort = struct.unpack('!H', udp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Destination Port:', destinationPort
        iStart = iEnd

        # prepare UDP Packet
        self.dialogPacket.sourcePort = sourcePort
        self.dialogPacket.destinationPort = destinationPort

        # 3. Length: 2 octet
        iEnd = iStart+2
        length = struct.unpack('!H', udp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Length:', length
        iStart = iEnd

        # 4. Checksum: 2 octet
        iEnd = iStart+2
        checksum = struct.unpack('!H', udp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'Checksum: 0x%x' % (checksum)
        iStart = iEnd

        # 5. Encapsulated Data
        encapsulatedDataLen = length-8
        iEnd = iStart+encapsulatedDataLen

        # prepare UDP Packet
        self.dialogPacket.data = udp[iStart:iEnd]

        if sourcePort in SIP_PORTS or destinationPort in SIP_PORTS:
            # prepare UDP Packet
            self.dialogPacket.udpType = UDP_TYPE_SIP
            self.__readSip(self.dialogPacket.data)
        else:
            # prepare UDP Packet
            self.dialogPacket.udpType = UDP_TYPE_UNKNOW

        # add to Packets List
        self.packetsList.append(self.dialogPacket)


    def __readSip(self, sip):
        """
        [Function]
        Read SIP content
        Note: this function only print the content of SIP packet

        [Argument]
        sip: the SIP packet data

        [Return]
        (N/A)

        [See Also]
        ########################################################
        # RFC 3261
        ########################################################
        """

        if '-vf' in sys.argv:
            print '-- SIP (Session Initiation Protocol) --'
            print sip


    def __readRtp(self, rtp, packetIndex):
        return parseRtp(rtp, self.telephoneEventPtInSdp, packetIndex)


    def __readPackets(self, fileName, fileobj):
        """
        [Function]
        Read every packets in the file until EOF

        [Argument]
        fileName: snoop file name
        fileobj: file object of snoop file

        [Return]
        (N/A)
        """

        while True:
            if not self.__readPacketRecord(fileobj):
                # deal with the packets when EOF

                self.__scanDialogPacketsList(fileName)

                # add the case to the list
                tempCaseData = CaseData()
                tempCaseData.snoopFileName = fileName
                tempCaseData.cacheName,tempDialogPacketsList = self.__dumpCaseToCache(fileName)
                tempCaseData.caseConfig = self.__getCaseConfig(fileName)
                self.caseList.append(tempCaseData)

                if '-vp' in sys.argv:
                    self.__printDialogPacketsList(len(self.caseList)-1, fileName, tempDialogPacketsList)
                break
            # else: continue reading the snoop file


    def __getCaseConfig(self, snoopFileName):
        """
        [Function]
        Get Case Config from SnoopFile's xml, e.g. the Snoop File Name is abc.snoop, then the Case Config File will be abc.xml

        [Argument]
        snoopFileName: snoop file name

        [Return]
        If has .xml file return CaseConfig, otherwise return None
        """

        xmlFileName = os.path.splitext(snoopFileName)[0]+'.xml'
        if not os.path.exists(xmlFileName):
            LOG.writeLog("There is no '%s'" % (xmlFileName))
            return None

        tempDom = minidom.parse(xmlFileName)
        tempRoot = tempDom.documentElement
        caseConfig = CaseConfig()

        tempCalledPrefix = tempRoot.getElementsByTagName('calledPrefix')
        if len(tempCalledPrefix)>0 and tempCalledPrefix[0].firstChild:
            caseConfig.calledPrefix = tempCalledPrefix[0].firstChild.data.strip()

        tempCalled = tempRoot.getElementsByTagName('called')
        if len(tempCalled)>0 and tempCalled[0].firstChild:
            caseConfig.called = tempCalled[0].firstChild.data.strip()

        tempCalling = tempRoot.getElementsByTagName('calling')
        if len(tempCalling)>0 and tempCalling[0].firstChild:
            caseConfig.calling = tempCalling[0].firstChild.data.strip()

        tempRedirect = tempRoot.getElementsByTagName('redirect')
        if len(tempRedirect)>0 and tempRedirect[0].firstChild:
            caseConfig.redirect = tempRedirect[0].firstChild.data.strip()

        tempReason = tempRoot.getElementsByTagName('reason')
        if len(tempReason)>0 and tempReason[0].firstChild:
            caseConfig.reason = tempReason[0].firstChild.data.strip()

        LOG.writeLog("-- The content of '%s' is as below --\n%s" % (xmlFileName, str(caseConfig)))
        return caseConfig


    def __dumpCaseToCache(self, snoopFileName):
        """
        [Function]
        Dump all packets of the case in the snoop file to a .dpl file (dialogPacketsList)

        [Argument]
        snoopFileName: snoop file name

        [Return]
        return (cacheName, dialogPacketsList)
        """

        caseInformation = CaseInformation()
        caseInformation.cifVersion = CIF_VERSION
        caseInformation.snoopFileName = snoopFileName
        tempFileStatus = os.stat(snoopFileName)
        caseInformation.snoopFileCreateTime = tempFileStatus.st_ctime
        caseInformation.snoopFileSize = tempFileStatus.st_size

        caseInformation.dialogNumbers = self.dialogNumbers

        cacheName = caseNameToCacheName(snoopFileName)
        cifFileName = cacheName + CASE_INFORMATION_FILE_EXT
        dplFileName = cacheName + DIALOG_PACKETS_LIST_FILE_EXT

        cacheDirName = os.path.split(cifFileName)[0]
        if not os.path.exists(cacheDirName):
            os.makedirs(cacheDirName)

        cifFile = file(cifFileName, 'wb')
        dplFile = file(dplFileName, 'wb')
        pickle.dump(caseInformation, cifFile)

        pickle.dump(self.dialogPacketsList, dplFile, 2)
        cifFile.close()
        dplFile.close()

        return (cacheName, self.dialogPacketsList)


    def __isDuplicatedIvrEvent(self, currentRtpTimestamp, currentIvrEventStr):
        """
        [Function]
        check whether this IVR event is duplicated

        [Argument]
        currentRtpTimestamp: current RTP's timestamp
        currentIvrEventStr: current IVR Event's content

        [Return]
        return True if duplicated, otherwise return False
        """

        if currentRtpTimestamp!=0:
            # 1. only need checking duplication when autotest=2
            # 2.1. the ivr event == the cached
            # 2.2. the timestamp <= the cached
            # 2.3. don't ignore the event whose timestamp is the same as the previous one
            if currentIvrEventStr==self.cachedIvrEventStr \
                    and currentRtpTimestamp<=self.cachedRtpTimestamp \
                        and self.ignoredIvrEventCount<IVR_EVENT_DUP_TIMES:
                self.ignoredIvrEventCount += 1
                return True
            else:
                self.cachedRtpTimestamp = currentRtpTimestamp
                self.cachedIvrEventStr = currentIvrEventStr
                self.ignoredIvrEventCount = 0
                return False
        else:
            return False


    def __scanDialogPacketsList(self, fileName):
        """
        [Function]
        Scan all packets to filter the useful ones (SIP & RTP),
        after scan, the useful dialog packet will be removed from the DialogPacketsList

        [Argument]
        fileName: name of this case's snoop file

        [Return]
        (N/A)
        """

        sipState = SIP_STATE_IDLE
        fromTag = ''
        toTag = ''
        callId = ''
        sessionSourcePort = 0
        sessionDestinationPort = 0

        # 1. scan packets list and indicate the useful packets

        # clear up something before scan the new case
        del self.dialogPacketsList[:]
        del self.dialogNumbers[:]
        self.cachedRtpTimestamp = -1
        self.cachedIvrEventStr = ''
        self.ignoredIvrEventCount = 0
        self.dialogIndex = -1

        tempData = ''
        i = 0
        for packet in self.packetsList:
            if sipState==SIP_STATE_IDLE:
                if packet.udpType==UDP_TYPE_SIP:
                    tempData = packet.data
                    reInvite = RE_SIP_INVITE.search(tempData)
                    if reInvite:
                        fromTag = getFromTag(tempData)
                        callId = getCallId(tempData)
                        sessionSourcePort = getSdpMediaPort(tempData)

                        self.dialogNumbers.append(DialogNumber(getCalledNumberFromRequestHead(reInvite), getCallingNumberFromContact(tempData)))

                        tempData = self.__templateInvite(tempData, reInvite)
                        tempData = self.__templateVia(tempData)
                        tempData = self.__templateFrom(tempData)
                        tempData = self.__templateTo(tempData)
                        tempData = self.__templateCallId(tempData)
                        tempData = self.__templateContact(tempData)
                        tempData = self.__templateCseqForInvite(tempData)
                        # needn't Record-Route
                        tempData = self.__deleteRecordRoute(tempData)
                        tempData = self.__templateContentLength(tempData)
                        tempData = self.__templateSdpM(tempData)
                        #tempData = self.__templateSdpO(tempData)
                        #tempData = self.__templateSdpC(tempData)
                        tempData = self.__templateSdpSourceIpAddress(tempData)

                        # Note: INVITE will begin a new dialog
                        self.dialogIndex += 1
                        self.packetsList[i].dialogIndex = self.dialogIndex
                        #print 'self.packetsList[%d].dialogIndex: %d' % (i, self.packetsList[i].dialogIndex)
                        self.packetsList[i].sipType = SIP_TYPE_INVITE
                        self.packetsList[i].data = tempData

                        # reset the cached RTP timestamp for the new dialog
                        self.cachedRtpTimestamp = -1
                        self.cachedIvrEventStr = ''
                        self.ignoredIvrEventCount = 0

                        sipState = SIP_STATE_WAITING_183

                i += 1
                continue

            if sipState==SIP_STATE_WAITING_183:
                if packet.udpType==UDP_TYPE_SIP:
                    tempData = packet.data
                    reResponse = RE_SIP_183.search(tempData)
                    if reResponse:
                        tempFromTag = getFromTag(tempData)
                        tempCallId = getCallId(tempData)

                        if tempFromTag==fromTag and tempCallId==callId:
                            toTag = getToTag(tempData)
                        else:
                            LOG.w("There is a 183 whose Call-ID (%s) does not equals INVITE's (%s)" %(tempCallId, callId))
                            i += 1
                            continue

                        sessionDestinationPort = getSdpMediaPort(tempData)
                        self.baseTimeTo183 = packet.timestamp
                        self.telephoneEventPtInSdp = getTelephoneEventPtFromSdp(tempData)
                        sipState = SIP_STATE_WAITING_200

                i += 1
                continue

            if sipState>=SIP_STATE_WAITING_200:
                if packet.udpType==UDP_TYPE_UNKNOW:
                    #print 'packet.sourcePort:', packet.sourcePort, 'packet.destinationPort:', packet.destinationPort
                    if packet.sourcePort==sessionSourcePort and packet.destinationPort==sessionDestinationPort:
                        self.packetsList[i].dialogIndex = self.dialogIndex
                        self.packetsList[i].received = False
                        self.packetsList[i].delttime = float(self.packetsList[i].timestamp) - float(self.baseTimeTo183)

                        tempPayloadType = 0
                        try:
                            tempPayloadType,tempRtpTimestamp,tempExtendedData = self.__readRtp(packet.data, self.packetsList[i].originalPacketIndex)
                        except:
                            i += 1
                            continue

                        self.packetsList[i].rtpTimestamp = tempRtpTimestamp
                        if tempPayloadType==self.telephoneEventPtInSdp:
                            self.packetsList[i].udpType = UDP_TYPE_RTP_EVENT
                            self.packetsList[i].dtmf = tempExtendedData
                        else:
                            self.packetsList[i].udpType = UDP_TYPE_RTP
                    elif packet.sourcePort==sessionDestinationPort and packet.destinationPort==sessionSourcePort:
                        tempPayloadType = 0
                        try:
                            tempPayloadType,tempRtpTimestamp,tempExtendedData = self.__readRtp(packet.data, self.packetsList[i].originalPacketIndex)
                        except:
                            i += 1
                            continue

                        self.packetsList[i].rtpTimestamp = tempRtpTimestamp

                        # only IVR Event type RTP need to save the following fields
                        if tempPayloadType==PAYLOAD_TYPE_IVR_RECORD_FILE:
                            tempIvrEventStr = tempExtendedData
                            if self.__isDuplicatedIvrEvent(tempRtpTimestamp, tempIvrEventStr):
                                i += 1
                                continue

                            self.packetsList[i].dialogIndex = self.dialogIndex
                            self.packetsList[i].received = True
                            self.packetsList[i].udpType = UDP_TYPE_RTP_IVR_RECORD_FILE
                            self.packetsList[i].ivrEventStr = tempIvrEventStr
                            # clear the data of received packet
                            self.packetsList[i].data = ''
                        elif tempPayloadType==PAYLOAD_TYPE_IVR_PROMPT:
                            tempIvrEventStr = str(tempExtendedData)
                            if self.__isDuplicatedIvrEvent(tempRtpTimestamp, tempIvrEventStr):
                                i += 1
                                continue

                            # Remove the original packet from packetsList, and then add the new ones to list
                            tempParentPacket = self.packetsList.pop(i)
                            tempParentPacket.dialogIndex = self.dialogIndex
                            tempParentPacket.received = True
                            # clear the data of received packet
                            tempParentPacket.data = ''
                            if len(tempExtendedData)>1:
                                tempParentPacket.isTwin = True

                            #print 'len(tempExtendedData):', len(tempExtendedData)

                            tempPromptIndex = len(tempExtendedData)
                            while tempPromptIndex>0:
                                tempPromptIndex -= 1

                                tempNewPrompt = copy.copy(tempParentPacket)

                                tempNewPrompt.udpType = tempExtendedData[tempPromptIndex][0] + UDP_TYPE_RTP_IVR_PROMPT
                                tempNewPrompt.ivrEventStr = tempExtendedData[tempPromptIndex][1]

                                self.packetsList.insert(i, tempNewPrompt)

                    i += 1
                    continue

            if sipState==SIP_STATE_WAITING_200:
                if packet.udpType==UDP_TYPE_SIP:
                    tempData = packet.data
                    reResponse = RE_SIP_200.search(tempData)
                    if reResponse:
                        tempFromTag = getFromTag(tempData)
                        tempToTag = getToTag(tempData)
                        tempCallId = getCallId(tempData)

                        if tempFromTag==fromTag and tempToTag==toTag and tempCallId==callId:
                            sipState = SIP_STATE_BEFORE_ACK
                        else:
                            i += 1
                            continue

                i += 1
                continue

            if sipState==SIP_STATE_BEFORE_ACK:
                if packet.udpType==UDP_TYPE_SIP:
                    tempData = packet.data
                    reAck = RE_SIP_ACK.search(tempData)
                    if reAck:
                        tempFromTag = getFromTag(tempData)
                        tempToTag = getToTag(tempData)
                        tempCallId = getCallId(tempData)

                        if tempFromTag==fromTag and tempToTag==toTag and tempCallId==callId:
                            tempData = self.__templateAck(tempData, reAck)
                            tempData = self.__templateVia(tempData)
                            tempData = self.__templateFrom(tempData)
                            tempData = self.__templateTo(tempData)
                            tempData = self.__templateCallId(tempData)
                            tempData = self.__templateContact(tempData)
                            tempData = self.__templateCseqForAck(tempData)

                            self.packetsList[i].dialogIndex = self.dialogIndex
                            self.packetsList[i].sipType = SIP_TYPE_ACK
                            self.packetsList[i].data = tempData

                            sipState = SIP_STATE_AFTER_ACK
                        else:
                            i += 1
                            continue

                i += 1
                continue

            if sipState==SIP_STATE_AFTER_ACK:
                if packet.udpType==UDP_TYPE_SIP:
                    tempData = packet.data
                    reBye = RE_SIP_BYE.search(tempData)
                    if reBye:
                        tempFromTag = getFromTag(tempData)
                        tempToTag = getToTag(tempData)
                        tempCallId = getCallId(tempData)

                        if tempFromTag==fromTag and tempToTag==toTag and tempCallId==callId:
                            # source says BYE
                            tempData = self.__templateBye(tempData, reBye)
                            tempData = self.__templateVia(tempData)
                            tempData = self.__templateFrom(tempData)
                            tempData = self.__templateTo(tempData)
                            tempData = self.__templateCallId(tempData)
                            tempData = self.__templateCseqForBye(tempData)
                            # needn't Route field
                            tempData = self.__deleteRoute(tempData)
                            # delete Diversion filed, and add later if need
                            tempData = self.__deleteDiversion(tempData)

                            self.packetsList[i].received = False
                            self.packetsList[i].dialogIndex = self.dialogIndex
                            self.packetsList[i].delttime = float(self.packetsList[i].timestamp) - float(self.baseTimeTo183)
                            self.packetsList[i].sipType = SIP_TYPE_BYE
                            self.packetsList[i].data = tempData

                            sipState = SIP_STATE_BYED
                        elif tempFromTag==toTag and tempToTag==fromTag and tempCallId==callId:
                            # destination says BYE
                            self.packetsList[i].received = True
                            self.packetsList[i].dialogIndex = self.dialogIndex
                            self.packetsList[i].sipType = SIP_TYPE_BYE
                            # clear the data of received packet
                            self.packetsList[i].data = ''

                            sipState = SIP_STATE_BYED
                        else:
                            i += 1
                            continue

                i += 1
                continue

            i += 1
            continue

        # 2. put all usable package to dialogPacktsList

        if self.dialogIndex < 0:
            LOG.a("There is no dialog found in '%s'" % (fileName))
            raise
        #else:

        tempDialogIndex = 0
        tempPacketsInADialog = []
        i = 0
        while True:
            if i >= len(self.packetsList):
                self.dialogPacketsList.append(tempPacketsInADialog[:])
                break

            if self.packetsList[i].dialogIndex==tempDialogIndex:
                tempPacketsInADialog.append(self.packetsList[i])
            elif self.packetsList[i].dialogIndex==tempDialogIndex+1:
                self.dialogPacketsList.append(tempPacketsInADialog[:])
                tempDialogIndex += 1
                # don't forget to add this dialog's first packet
                tempPacketsInADialog = [self.packetsList[i]]
            elif self.packetsList[i].dialogIndex<0:
                pass
            else:
                LOG.a("Invalid dialog index %d when process '%s' dialg index %d" % (self.packetsList[i].dialogIndex, fileName, tempDialogIndex))
                raise

            i += 1

        # clear it up after all items in packetsList have been put into dialogPacketsList
        del self.packetsList[:]


    def __printDialogPacksList(self):
        """
        [Function]
        Print packet list for debug

        [Argument]
        (N/A)

        [Return]
        (N/A)
        """

        print 'There are', len(self.dialogPacketsList), 'dialogs in this list'

        tempDialogIndex = 0
        tempPacketIndex = 0
        for dialog in self.dialogPacketsList:
            print '-'*70, '-vp -- dialog:', str(tempDialogIndex), '--'

            for packet in dialog:
                print '-'*70, '-vp --', i, '--'
                print str(packet)
                print
                tempPacketIndex += 1

            tempDialogIndex += 1


    def __templateInvite(self, data, reInvite):
        try:
            temp = RE_SIP_URI.sub(MAGIC_SIP_URI, reInvite.group())
            return data[0:reInvite.start()] + RE_EMAIL.sub('[CALLED]@[DESTINATION]', temp) + data[reInvite.end():]
        except:
            LOG.e('__templateInvite except:\n%s' % (data))
            return data


    def __templateAck(self, data, reAck):
        try:
            temp = RE_IP_AND_PORT.sub(MAGIC_IP_AND_PORT, reAck.group())
            return data[0:reAck.start()] + RE_IP.sub('[DESTINATION]', temp) + data[reAck.end():]
        except:
            LOG.e('__templateAck except:\n%s' % (data))
            return data


    def __templateBye(self, data, reBye):
        try:
            temp = RE_IP_AND_PORT.sub(MAGIC_IP_AND_PORT, reBye.group())
            return data[0:reBye.start()] + RE_IP.sub('[DESTINATION]', temp) + data[reBye.end():]
        except:
            LOG.e('__templateBye except:\n%s' % (data))
            return data


    def __templateFromDisplay(self, fromStr):
        if RE_SIP_FROM_DISPLAY.search(fromStr):
            return RE_SIP_FROM_DISPLAY.sub('[FROM_DISPLAY]', fromStr)
        else:
            return fromStr


    def __templateFrom(self, data):
        reFrom = RE_SIP_FROM.search(data)
        #print 'reFrom:', reFrom.group()

        if RE_EMAIL.search(reFrom.group()):
            try:
                #print RE_EMAIL.search(reFrom.group()).group()
                return data[0:reFrom.start()] + self.__templateFromDisplay(RE_SIP_TAG.sub('tag=[FROM_TAG]', RE_EMAIL.sub('[FROM_CALLING]@[SOURCE]', reFrom.group()))) + data[reFrom.end():]
            except:
                LOG.e('__templateFrom except 1:\n%s' % (data))
                return data
        elif RE_IP.search(reFrom.group()):
            try:
                return data[0:reFrom.start()] + self.__templateFromDisplay(RE_SIP_TAG.sub('tag=[FROM_TAG]', RE_IP.sub('[FROM_CALLING]@[SOURCE]', reFrom.group()))) + data[reFrom.end():]
            except:
                LOG.e('__templateFrom except 2:\n%s' % (data))
                return data
        else:
            LOG.e('cannot parse reFrom with RE_EMAIL and RE_IP: %s' % (reFrom.group()))
            return data


    def __templateVia(self, data):
        reAllVia = RE_SIP_VIA.finditer(data)
        vs = []
        first = True
        theFirstSpan = ()
        theFirstVia = ''
        for v in reAllVia:
            if first:
                theFirstSpan = v.span()
                theFirstVia = data[theFirstSpan[0]:theFirstSpan[1]+1]
                first = False
            else:
                vs.insert(0, v.span())

        tempData = data
        for span in vs:
            # remove VIAs to leave the first one
            tempData = tempData[0:span[0]] + tempData[span[1]+1:]

        try:
            temp = RE_IP_AND_PORT.sub(MAGIC_IP_AND_PORT, theFirstVia)
            return tempData[0:theFirstSpan[0]] + RE_IP.sub('[SOURCE]', temp) + tempData[theFirstSpan[1]+1:]
        except:
            LOG.e('__templateVia except:\n%s' % (data))
            return data


    def __templateContact(self, data):
        reContact = RE_SIP_CONTACT.search(data)

        try:
            if RE_EMAIL.search(reContact.group()):
                try:
                    temp = RE_SIP_URI.sub(MAGIC_SIP_URI, reContact.group())
                    return data[0:reContact.start()] + RE_EMAIL.sub('[CALLING]@[SOURCE]', temp) + data[reContact.end():]
                except:
                    LOG.e('__templateContact except 1:\n%s' % (data))
                    return data
            elif RE_IP.search(reContact.group()):
                try:
                    temp = RE_SIP_URI.sub(MAGIC_SIP_URI, reContact.group())
                    return data[0:reContact.start()] + RE_IP.sub('[CALLING]@[SOURCE]', temp) + data[reContact.end():]
                except:
                    LOG.e('__templateContact except 2:\n%s' % (data))
                    return data
            else:
                LOG.e('cannot parse reContact with RE_EMAIL and RE_IP: %s' % (reContact.group()))
                return data
        except:
            LOG.e('__templateContact except 3:\n%s' % (data))
            return data


    def __templateCseqForInvite(self, data):
        reCseq = RE_SIP_CSEQ.search(data)
        try:
            # Note: reCseq.end()-1 is used to hold \r
            return data[0:reCseq.start()] + 'CSeq: 1 INVITE' + data[reCseq.end()-1:]
        except:
            LOG.e('__templateCseqForInvite except:\n%s' % (data))
            return data


    def __templateCseqForAck(self, data):
        reCseq = RE_SIP_CSEQ.search(data)
        try:
            # Note: reCseq.end()-1 is used to hold \r
            return data[0:reCseq.start()] + 'CSeq: 1 ACK' + data[reCseq.end()-1:]
        except:
            LOG.e('__templateCseqForAck except:\n%s' % (data))
            return data


    def __templateCseqForBye(self, data):
        reCseq = RE_SIP_CSEQ.search(data)
        try:
            # Note: reCseq.end()-1 is used to hold \r
            return data[0:reCseq.start()] + 'CSeq: 2 BYE' + data[reCseq.end()-1:]
        except:
            LOG.e('__templateCseqForBye except:\n%s' % (data))
            return data


    def __templateTo(self, data):
        reTo = RE_SIP_TO.search(data)

        if RE_EMAIL.search(reTo.group()):
            try:
                temp = RE_SIP_URI.sub(MAGIC_SIP_URI, reTo.group())
                return data[0:reTo.start()] + RE_SIP_TAG.sub('tag=[TO_TAG]', RE_EMAIL.sub('[CALLED]@[DESTINATION]', temp)) + data[reTo.end():]
            except:
                LOG.e('__templateTo except:\n%s' % (data))
                return data
        elif RE_IP.search(reTo.group()):
            try:
                temp = RE_SIP_URI.sub(MAGIC_SIP_URI, reTo.group())
                return data[0:reTo.start()] + RE_SIP_TAG.sub('tag=[TO_TAG]', RE_IP.sub('[CALLED]@[DESTINATION]', temp)) + data[reTo.end():]
            except:
                LOG.e('__templateTo except:\n%s' % (data))
                return data


    def __templateCallId(self, data):
        reCallId = RE_SIP_CALL_ID.search(data)
        strCallId = reCallId.group()

        if RE_EMAIL.search(strCallId):
            try:
                return data[0:reCallId.start()] + RE_EMAIL.sub('[FROM_TAG]@[SOURCE]', reCallId.group()) + data[reCallId.end():]
            except:
                LOG.e('__templateCallId except 1:\n%s' % (data))
                return data
        else:
            try:
                return data[0:reCallId.start()] + 'Call-ID: [FROM_TAG]@[SOURCE]' + data[reCallId.end():]
            except:
                LOG.e('__templateCallId except 2:\n%s' % (data))
                return data


    def __templateContentLength(self, data):
        reContentLength = RE_SIP_CONTENT_LENGTH.search(data)
        try:
            return data[0:reContentLength.start()] + 'Content-Length: [LENGTH]' + data[reContentLength.end():]
        except:
            LOG.e('__templateContentLength except:\n%s' % (data))
            return data


    def __deleteRoute(self, data):
        reRoute = RE_SIP_ROUTE.search(data)
        try:
            tempStart = reRoute.start()
            if data[tempStart-1] == '\n':
                if data[tempStart-2] == '\r':
                    tempStart = tempStart-2
                else:
                    tempStart = tempStart-1
            return data[0:tempStart] + data[reRoute.end():]
        except:
            return data


    def __deleteDiversion(self, data):
        reDiversion = RE_SIP_DIVERSION.search(data)
        try:
            tempStart = reDiversion.start()
            if data[tempStart-1] == '\n':
                if data[tempStart-2] == '\r':
                    tempStart = tempStart-2
                else:
                    tempStart = tempStart-1
            return data[0:tempStart] + data[reDiversion.end():]
        except:
            return data


    def __deleteRecordRoute(self, data):
        reRecordRoute = RE_SIP_RECORD_ROUTE.search(data)
        try:
            tempStart = reRecordRoute.start()
            if data[tempStart-1] == '\n':
                if data[tempStart-2] == '\r':
                    tempStart = tempStart-2
                else:
                    tempStart = tempStart-1
            return data[0:tempStart] + data[reRecordRoute.end():]
        except:
            return data


    def __templateSdpSourceIpAddress(self, data):
        reV = RE_SDP_V.search(data)

        strSdp = ''
        posSdp = 0
        try:
            psSdp = reV.start()
            strSdp = data[reV.start():]
        except:
            return data

        try:
            return data[0:psSdp] + RE_IP.sub('[SOURCE]', strSdp)
        except:
            return data

    def __templateSdpO(self, data):
        reO = RE_SDP_O.search(data)
        try:
            return data[0:reO.start()] + RE_IP.sub('[SOURCE]', reO.group()) + data[reO.end():]
        except:
            LOG.e('__templateSdpO except:\n%s' % (data))
            return data


    def __templateSdpM(self, data):
        reM = RE_SDP_M.search(data)
        try:
            return data[0:reM.start()] + RE_SDP_M_AUDIO.sub('audio [AUDIO_PORT]', reM.group()) + data[reM.end():]
        except:
            LOG.e('__templateSdpM except:\n%s' % (data))
            return data


def washIvrPromptStr(ivrPromptStr, udpType=UDP_TYPE_RTP_IVR_SPEAK_PROMPT, completely=True):
    """
    [Function]
    wash IVR prompt string to make it only file name

    [Argument]
    ivrPromptStr: IVR prompt string
    udpType: the udp type of this packet, default is UDP_TYPE_RTP_IVR_SPEAK_PROMPT
    completely: need transfer the prompt string to lower? default is True

    [Return]
    (udpType, the-washed-IVR-prompt-string)
    """

    tempIvrPromptStr = ivrPromptStr.replace('\\', '/')
    try:
        tempIvrPromptStr = tempIvrPromptStr[tempIvrPromptStr.rindex('/')+1:]
    except ValueError:
        LOG.w("There is no '\\' or '/' in IVR prompt string")

    if completely:
        tempIvrPromptStr = tempIvrPromptStr.lower()

    if udpType!=UDP_TYPE_RTP_IVR_SPEAK_PROMPT:
        return (udpType, tempIvrPromptStr)
    #else:

    # There is a bug in IVR autotest !!!
    if len(tempIvrPromptStr)>8 and (tempIvrPromptStr.find('!')>=0 \
            or tempIvrPromptStr.find('@')>=0 \
            or tempIvrPromptStr.find('#')>=0 \
            or tempIvrPromptStr.find('$')>=0 \
            or tempIvrPromptStr.find('%')>=0 \
            or tempIvrPromptStr.find('^')>=0 \
            or tempIvrPromptStr.find('&')>=0 \
            or tempIvrPromptStr.find('*')>=0 \
            or tempIvrPromptStr.find('(')>=0 \
            or tempIvrPromptStr.find(')')>=0 \
            or tempIvrPromptStr.find('-')>=0 \
            or tempIvrPromptStr.find('+')>=0 \
            or tempIvrPromptStr.find('=')>=0):
        LOG.w("This string '%s' seems a record file" % (tempIvrPromptStr))
        return (UDP_TYPE_RTP_IVR_RECORD_FILE, tempIvrPromptStr)
    if len(tempIvrPromptStr)>5 and tempIvrPromptStr[1].isdigit():
        tempIvrPromptStr = tempIvrPromptStr[2:]
    else:
        LOG.w("This string '%s' seems not a prompt" % (tempIvrPromptStr))

    return (UDP_TYPE_RTP_IVR_SPEAK_PROMPT, tempIvrPromptStr)


def getResponseCode(data):
    reResponse = RE_SIP_RESPONSE.search(data)
    strResponse = reResponse.group()
    reResponseCode = RE_SIP_RESPONSE_CODE.search(strResponse)
    strResponseCode = reResponseCode.group()
    return strResponseCode


def getToTag(data):
    reTo = RE_SIP_TO.search(data)
    strTo = reTo.group()
    reTag = RE_SIP_TAG.search(strTo)

    try:
        strTag = reTag.group()
        return strTag[strTag.index('=')+1:].strip()
    except:
        return ''


def getSdpMediaPort(data):
    strM = RE_SDP_M.search(data).group()
    strAudio = RE_SDP_M_AUDIO.search(strM).group()
    return int(RE_INT.search(strAudio).group())


def getTelephoneEventStr(data):
    return RE_SDP_TELEPHONE_EVENT.search(data).group()


def getTelephoneEventPtFromSdp(data):
    strTelephoneEvent = RE_SDP_TELEPHONE_EVENT.search(data).group()
    strRtpmap = RE_SDP_RTPMAP.search(strTelephoneEvent).group()
    return int(RE_INT.search(strRtpmap).group())


def getFmtpForTelephoneEvent(data, telephoneEventPt):
    re_fmtp_telephone_event = re.compile(r'a=fmtp:%d.*' % (telephoneEventPt))
    return re_fmtp_telephone_event.search(data).group()


def getFromTag(data):
    reFrom = RE_SIP_FROM.search(data)
    strFrom = reFrom.group()
    reTag = RE_SIP_TAG.search(strFrom)
    strTag = reTag.group()

    return strTag[strTag.index('=')+1:].strip()


def getCallId(data):
    reCallId = RE_SIP_CALL_ID.search(data)
    strCallId = reCallId.group()

    try:
        tempAtPos = strCallId.index('@')
        return strCallId[strCallId.index(':')+1:tempAtPos].strip()
    except ValueError:
        return strCallId[strCallId.index(':')+1:].strip()


def getCallIdStr(data):
    return RE_SIP_CALL_ID.search(data).group()


def getCSeqStr(data):
    return RE_SIP_CSEQ.search(data).group()


def getFromStr(data):
    return RE_SIP_FROM.search(data).group()


def getToStr(data):
    return RE_SIP_TO.search(data).group()


def getSipSdp(data):
    reV = RE_SDP_V.search(data)
    try:
        return data[0:reV.start()].strip(), data[reV.start():].strip()
    except:
        return data, ''


def getViasList(data):
    return RE_SIP_VIA.findall(data)


def getCalledNumberFromRequestHead(reInvite):
    reSipUri = RE_EMAIL.search(reInvite.group())
    strSipUri = reSipUri.group()

    try:
        tempAtPos = strSipUri.index('@')
        return strSipUri[:tempAtPos].strip()
    except ValueError:
        return strSipUri.strip()


def getCalledNumberFromRequestHead2(data):
    reInvite = RE_SIP_INVITE.search(data)
    reSipUri = RE_EMAIL.search(reInvite.group())
    strSipUri = reSipUri.group()

    try:
        tempAtPos = strSipUri.index('@')
        return strSipUri[:tempAtPos].strip()
    except ValueError:
        return strSipUri.strip()


def getCallingNumberFromContactOrFrom(data):
    strNumber = getCallingNumberFromContact(data)
    if strNumber=='':
        return getCallingNumberFromFrom(data)
    else:
        return strNumber


def getCallingNumberFromContact(data):
    reContact = RE_SIP_CONTACT.search(data)
    reSipUri = RE_EMAIL.search(reContact.group())
    strSipUri = ''
    try:
        strSipUri = reSipUri.group()
    except AttributeError:
        return ''

    try:
        tempAtPos = strSipUri.index('@')
        return strSipUri[:tempAtPos].strip()
    except ValueError:
        return strSipUri.strip()


def getCallingNumberFromFrom(data):
    reFrom = RE_SIP_FROM.search(data)
    reSipUri = RE_EMAIL.search(reFrom.group())
    strSipUri = ''
    try:
        strSipUri = reSipUri.group()
    except AttributeError:
        return ''

    try:
        tempAtPos = strSipUri.index('@')
        return strSipUri[:tempAtPos].strip()
    except ValueError:
        return strSipUri.strip()


def getIpAddressFromRequestHead(data):
    reInvite = RE_SIP_INVITE.search(data)

    try:
        reIpAddress = RE_IP.search(reInvite.group())
        return reIpAddress.group().strip()
    except ValueError:
        reSipUri = RE_EMAIL.search(reInvite.group())
        strSipUri = reSipUri.group()
        tempAtPos = strSipUri.index('@')
        return strSipUri[tempAtPos+1:].strip()


def getContactStr(data):
    return RE_SIP_CONTACT.search(data).group()


def setTelephoneEventPt(data, pt):
    mp = data[1]
    tempMp = chr(ord(mp)&0x80 + pt)
    return data[0]+tempMp+data[2:]


def quicklyGetPt(rtp):
    """
    please refer to parseRtp
    """

    try:
        mp = struct.unpack('B', rtp[1:2])[0]
        return int(mp & 0x7f)
    except:
        return -1


def quicklyGetTimestamp(rtp):
    """
    please refer to parseRtp
    """

    try:
        timestamp = struct.unpack('!I', rtp[4:8])[0]
        return int(timestamp)
    except:
        return -1


def parseRtp(rtp, telephoneEventPtInSdp=None, packetIndex=None):
    """
    [Function]
    Parse RTP content

    [Argument]
    rtp: the RTP packet data
    telephoneEventPtInSdp: 2833's payload type in SDP
    packetIndex: packet index, used for debug to print the packet index

    [Return]
    payloadType, rtpTimestamp, extendedData
    Note:
    1. if payload is 2833, extendedData will be event
    2. if payload is IVR private record file event, extendedData will be Record File
    3. if payload is IVR private prompt, extendedData will be a tuple (promptType, prompt)
    3. otherwise extendedData will be None

    [See Also]
    ########################################################
    # RFC 3550
    # http://www.rfc-editor.org/rfc/rfc3550.txt
    ########################################################
    """

    if '-vf' in sys.argv:
        print
        print '-'*50, ' RTP --',
        if packetIndex:
            print str(packetIndex), '--'

    iStart = 0
    iEnd = 0

    # 1. version (V): 2 bits
    # 2. padding (P): 1 bit
    # 3. extension (X): 1 bit
    # 4. CSRC count (CC): 4 bits
    # = 1 octet
    iEnd = iStart+1
    vpec = struct.unpack('B', rtp[iStart:iEnd])[0]

    version = vpec >> 6
    if '-vf' in sys.argv:
        print 'version:', version

    padding = (vpec >> 5) & 0x1
    if '-vf' in sys.argv:
        print 'padding:', padding

    extension = (vpec >> 4) & 0x1
    if '-vf' in sys.argv:
        print 'extension:', extension

    cc = vpec & 0xf
    if '-vf' in sys.argv:
        print 'CSRC count:', cc
    iStart = iEnd

    # 5. marker (M): 1 bit
    # 6. payload type (PT): 7 bits
    # = 1 octet
    iEnd = iStart+1
    mp = struct.unpack('B', rtp[iStart:iEnd])[0]

    marker = mp >> 7
    if '-vf' in sys.argv:
        print 'marker:', marker

    pt = mp & 0x7f
    if '-vf' in sys.argv:
        print 'payload type (PT):', pt
    iStart = iEnd

    # 7. sequence number: 16 bits (2 octet)
    iEnd = iStart+2
    sequenceNumber = struct.unpack('!H', rtp[iStart:iEnd])[0]
    if '-vf' in sys.argv:
        print 'sequence number:', sequenceNumber
    iStart = iEnd

    # 8. timestamp: 32 bits (4 octet)
    iEnd = iStart+4
    timestamp = struct.unpack('!I', rtp[iStart:iEnd])[0]
    if '-vf' in sys.argv:
        print 'timestamp:', timestamp
    iStart = iEnd

    # 9. SSRC: 32 bits (4 octet)
    iEnd = iStart+4
    ssrc = struct.unpack('!I', rtp[iStart:iEnd])[0]
    if '-vf' in sys.argv:
        print 'SSRC:', ssrc
    iStart = iEnd

    # 10. CSRC list: 0 to 15 items, 32 bits each
    if cc>15:
        if '-vf' in sys.argv:
            print 'CSRC count overflow'
        raise 'CSRC count overflow'

    if cc>0:
        csrcIndex = 0
        while csrcIndex < cc-1:
            iEnd = iStart+4
            csrc = struct.unpack('!I', rtp[iStart:iEnd])[0]
            if '-vf' in sys.argv:
                print 'CSRC - ', csrcIndex, ':', csrc
            csrcIndex += 1
            iStart = iEnd

    # 11. RTP Header Extension
    if extension==1:
        if '-vf' in sys.argv:
            print 'RTP Header Extension -'

        # 11.1. defined by profile: 2 octet
        iEnd = iStart+2
        dbp = struct.unpack('B'*2, rtp[iStart:iEnd])
        if '-vf' in sys.argv:
            print 'defined by profile:', dbp
        iStart = iEnd

        # 11.2. length: 2 octet
        iEnd = iStart+2
        length = struct.unpack('!H', rtp[iStart:iEnd])[0]
        if '-vf' in sys.argv:
            print 'length:', length
        iStart = iEnd

        extensionIndex = 0
        while extensioinIndex < length:
            iEnd = iStart+4
            extensionData = struct.unpack('B'*4, rtp[iStart:iEnd])
            if '-vf' in sys.argv:
                print 'extension -', extensionIndex, ':', extensionData
            extensionIndex += 1
            iStart = iEnd

    # 12. payload
    payload = rtp[iStart:]

    if pt==telephoneEventPtInSdp:
        tempEvent = parse2833Event(payload)
        return (pt, timestamp, tempEvent)
    elif pt==PAYLOAD_TYPE_G711:
        if '-vf' in sys.argv:
            print 'G.711 payload:'
            print tuple2Hex(struct.unpack('B'*len(payload), payload))
        return (pt, timestamp, None)
    elif pt==PAYLOAD_TYPE_IVR_RECORD_FILE:
        tempRecordFile = parseRecordFileEvent(payload)
        return (pt, timestamp, tempRecordFile)
    elif pt==PAYLOAD_TYPE_IVR_PROMPT:
        tempPromptList = parsePromptEvent(payload)
        return (pt, timestamp, tempPromptList)
    elif pt==PAYLOAD_TYPE_COMFORT_NOISE:
        return (pt, timestamp, None)
    else:
        LOG.i('Unknow payloadtype %d' % (pt))
        return (pt, timestamp, None)


def parse2833Event(payload):
    """
    [Function]
    Parse 2833 RTP event's content

    [Argument]
    payload: the payload content data

    [Return]
    2833 event

    [See Also]
    ########################################################
    # RFC 2833
    # http://www.faqs.org/rfcs/rfc2833.html
    ########################################################
    """

    if '-vf' in sys.argv:
        print '-- RFC2833 --'

    iStart = 0
    iEnd = 0

    # 1. event: 1 octet
    iEnd = iStart+1
    event = struct.unpack('B', payload[iStart:iEnd])[0]
    if '-vf' in sys.argv:
        print 'event:', event
    iStart = iEnd

    # 2. End of Event: 1 bit
    # 3. Reserved: 1 bit
    # 4. Volume: 6 bits
    # = 1 octet
    iEnd = iStart+1
    erv = struct.unpack('B', payload[iStart:iEnd])[0]

    eoe = erv >> 7
    if '-vf' in sys.argv:
        print 'End of Event:', eoe

    reserved = (erv >> 6) & 0x1
    if '-vf' in sys.argv:
        print 'Reserved:', reserved

    volume = erv & 0x3f
    if '-vf' in sys.argv:
        print 'Volume:', volume
    iStart = iEnd

    # 5. duration: 2 octet
    iEnd = iStart+2
    duration = struct.unpack('!H', payload[iStart:iEnd])[0]
    if '-vf' in sys.argv:
        print 'duration:', duration
    iStart = iEnd

    return event


def parseRecordFileEvent(payload):
    """
    [Function]
    Parse IVR's private Record File Event

    [Argument]
    payload: the payload content data

    [Return]
    Record File
    """

    tempRecordFile = str(payload[1:])
    tempEndPos = tempRecordFile.find('\0')
    tempRecordFile = tempRecordFile[0:tempEndPos]
    if '-vf' in sys.argv:
        print 'Record File:', tempRecordFile

    return tempRecordFile


def parsePromptEvent(payload):
    """
    [Function]
    Parse IVR's private Prompt Event

    [Argument]
    payload: the payload content data

    [Return]
    a list of tuple (promptType, prompt)
    """

    tempList = []
    tempPromptCount = struct.unpack('B', payload[0])[0]
    #print 'tempPromptCount: %d' % (tempPromptCount)

    tempPayloadList = payload[1:].strip().split('\0')
    # remove all empty line in the list
    while True:
        try:
            tempPayloadList.remove('')
        except ValueError:
            break

    if len(tempPayloadList)<tempPromptCount:
        LOG.a('Lack prompt(s) in the payload')
        raise

    tempPrompt = ''
    tempPromptIndex = 0

    while tempPromptIndex<tempPromptCount:
        tempPrompt = tempPayloadList[tempPromptIndex]
        tempPromptIndex += 1

        if '-vf' in sys.argv:
            print 'Prompt:', tempPrompt

        if tempPrompt.find('speak.vox')>-1:
            tempList.append((PROMPT_TYPE_SPEAK, tempPrompt))
        elif tempPrompt.find('system32.vox')>-1:
            tempList.append((PROMPT_TYPE_SYSTEM, tempPrompt))
        elif tempPrompt.find('rectone')>-1:
            tempList.append((PROMPT_TYPE_RECORD_TONE, tempPrompt))
        else:
            LOG.e('Unknow Prompt Type: %s' % (tempPrompt))

    return tempList


def caseNameToCacheName(fileName):
    """
    [Function]
    Change case name to cache name, e.g. /home/anthony/simulators/sip/voicebird/case/auto.snoop => /home/anthony/simulators/sip/voicebird/cache/auto

    [Argument]
    fileName: the file name which in the dir case

    [Return]
    return cache name in the dir cache
    """

    absPathOfDirCase = os.path.abspath(DIR_CASE)
    absPathOfDirCache = os.path.abspath(DIR_CACHE)

    #print 'absPathOfDirCase:', absPathOfDirCase
    #print 'absPathOfDirCache:', absPathOfDirCache
    #print 'fileName:', fileName

    cacheName = os.path.splitext(absPathOfDirCache + fileName.replace(absPathOfDirCase, ''))[0]

    #print 'cacheName:', cacheName

    return cacheName


def cacheNameToCaseName(fileName):
    """
    [Function]
    Change cache name to case name, e.g. /home/anthony/simulators/sip/voicebird/cache/auto.sfi => /home/anthony/simulators/sip/voicebird/case/auto

    [Argument]
    fileName: the file name which in the dir cache

    [Return]
    return case name in the dir cache
    """

    absPathOfDirCase = os.path.abspath(DIR_CASE)
    absPathOfDirCache = os.path.abspath(DIR_CACHE)

    caseName = os.path.splitext(absPathOfDirCase + fileName.replace(absPathOfDirCache, ''))[0]
    return caseName


def loadCaseInfoFromCase(snoopFileName):
    return loadCaseInfoFromCache(caseNameToCacheName(snoopFileName))


def loadCaseInfoFromCache(cacheName):
    """
    [Function]
    Load CaseInformation from cache

    [Argument]
    cacheName: cache name, e.g. /home/anthony/simulators/sip/voicebird/cache/auto

    [Return]
    return CaseInformation if exist, otherwise return None
    """

    cifFileName = cacheName+CASE_INFORMATION_FILE_EXT

    if os.path.exists(cifFileName):
        cifFile = file(cifFileName, 'rb')
        sfi = pickle.load(cifFile)
        cifFile.close()
        return sfi
    else:
        return None


def getDialogNumbersFromCache(cacheName):
    cif = loadCaseInfoFromCache(cacheName)

    return cif.dialogNumbers


def loadDialogPacketsListFromCache(cacheName):
    """
    [Function]
    Load DialogPacketsList from cache

    [Argument]
    cacheName: cache name, e.g. /home/anthony/simulators/sip/voicebird/cache/auto

    [Return]
    return DialogPacketsList
    """

    dplFileName = cacheName+DIALOG_PACKETS_LIST_FILE_EXT

    dplFile = file(dplFileName, 'rb')
    dpl = pickle.load(dplFile)
    dplFile.close()

    LOG.i("'%s' has %d dialogs" % (dplFileName, len(dpl)))

    return dpl


fuzzyPromptsDict = {}
def getFuzzyPrompts():
    """
    [Function]
    get fuzzy prompts from fuzzy prompts config file

    [Argument]
    (N/A)

    [Return]
    (N/A)
    """

    if not os.path.exists(FUZZY_PROMPTS_FILE):
        LOG.i("There is no '%s'" % (FUZZY_PROMPTS_FILE))
        return

    fileobj = file(FUZZY_PROMPTS_FILE, 'r')

    try:
        while True:
            tempPair = fileobj.readline()
            # EOF
            if not tempPair:
                break
            # else:

            tempPair = tempPair.strip().lower()
            if tempPair.startswith(ANNOTATION_CHAR) or len(tempPair)==0:
                continue

            tempElements = tempPair.split(':')
            for element in tempElements:
                fuzzyPromptsDict[element] = tempElements

        if len(fuzzyPromptsDict)>0:
            LOG.writeLog('-- Fuzzy Prompts Dict --\n' + str(fuzzyPromptsDict))
        else:
            LOG.i('There is no fuzzy prompts defined')
    finally:
        fileobj.close()


callParameters = None
def getParameters():
    """
    [Function]
    Get parameters from command input

    [Argument]
    (N/A)

    [Return]
    (N/A)
    """

    global callParameters

    useDefault = False
    # PARAMETER -y: Yes, means all to say yes for the questions
    gotYes = ('-y' in sys.argv) and os.path.exists(CALL_PARAMETERS_CONFIG_FILE)

    try:
        parameterFile = file(CALL_PARAMETERS_CONFIG_FILE, 'rb')
        parameters = pickle.load(parameterFile)

        while not gotYes:
            yesOrNo = raw_input('Do you want to use the old Call Parameters? [Y/N, default N]: ').strip().upper()
            if yesOrNo=='':
                yesOrNo = 'N'

            if yesOrNo=='Y':
                useDefault = True
                break
            elif yesOrNo=='N':
                useDefault = False
                break
        else:
            useDefault = True

        parameterFile.close()
    except KeyboardInterrupt:
        raise KeyboardInterrupt
    except:
        # there is no config file found
        parameters = Parameters()
        print 'Please setup the following Call Parameters.'

    if useDefault:
        callParameters = parameters
        return
    #else:

    while True:
        tempDestination = raw_input('[ Mandatory ] The DESTINATION machine IP address or machine name [%s]: ' % (parameters.destination))
        if tempDestination=='':
            tempDestination = parameters.destination

        tempDestination = tempDestination.strip()
        try:
            if tempDestination=='':
                raise 'Empty destination'
            socket.gethostbyname(tempDestination)
        except KeyboardInterrupt:
            raise KeyboardInterrupt
        except:
            print 'DESTINATION is invalid, please try again'
        else:
            break

    tempCalledPrefix = raw_input("[ Optional  ] The called/redirect's PREFIX [%s]: " % (parameters.calledPrefix))
    if tempCalledPrefix=='':
        tempCalledPrefix = parameters.calledPrefix
    tempCalledPrefix = tempCalledPrefix.strip()

    while True:
        tempCalledCount = raw_input('[ Mandatory ] How many called number? [%d]: ' % (parameters.calledCount))
        if tempCalledCount=='':
            tempCalledCount = str(parameters.calledCount)

        tempCalledCount = tempCalledCount.strip()
        if tempCalledCount.isdigit():
            tempCalledCount = int(tempCalledCount)
            if tempCalledCount<1:
                print 'The min count is 1, please try again'
                continue
            else:
                break
        else:
            print 'The COUNT must be a digit, please try again'
            continue

    while True:
        tempCalled = raw_input('[ Mandatory ] The CALLED phone number [%s]: ' % (parameters.called))
        if tempCalled=='':
            tempCalled = parameters.called

        tempCalled = tempCalled.strip()

        if tempCalledCount<=1:
            if tempCalled=='':
                print 'CALLED is invalid, please try again'
                contiue
            else:
                break
        else:
            if not tempCalled.isdigit():
                print 'The called count is bigger than 1, so please make sure the begin called number is a digit'
                continue
            else:
                break

    while True:
        tempSource = raw_input('[ Mandatory ] The SOURCE machine IP address [%s]: ' % (parameters.source))
        if tempSource=='':
            tempSource = parameters.source

        tempSource = tempSource.strip()
        try:
            if RE_IP.search(tempSource).group()!=tempSource:
                raise 'Invalid source'

            socket.gethostbyname(tempSource)
        except KeyboardInterrupt:
            raise KeyboardInterrupt
        except:
            print 'SOURCE is invalid, please try again'
        else:
            break

    tempCalling = raw_input('[ Optional  ] The CALLING phone number [%s]: ' % (parameters.calling))
    if tempCalling=='':
        tempCalling = parameters.calling
    tempCalling = tempCalling.strip()

    while True:
        tempRedirectCount = raw_input('[ Mandatory ] How many redirect number? [%d]: ' % (parameters.redirectCount))
        if tempRedirectCount=='':
            tempRedirectCount = str(parameters.redirectCount)

        tempRedirectCount = tempRedirectCount.strip()
        if tempRedirectCount.isdigit():
            tempRedirectCount = int(tempRedirectCount)
            if tempRedirectCount<0:
                print 'The min count is 0, please try again'
                continue
            else:
                break
        else:
            print 'The COUNT must be a digit, please try again'
            continue

    if tempRedirectCount>0:
        while True:
            tempRedirect = raw_input('[ Mandatory ] The REDIRECT number [%s]: ' % (parameters.redirect))
            if tempRedirect=='':
                tempRedirect = parameters.redirect
            tempRedirect = tempRedirect.strip()

            if tempRedirectCount==1:
                break
            else:
                if not tempRedirect.isdigit():
                    print 'The redirect count is bigger than 1, so please make sure the begin redirect number is a digit'
                    continue

        if parameters.reason.strip()!='':
            tempReason = raw_input('[ Mandatory ] The redirect REASON [unknown, user-busy, no-answer, unavailable, unconditional, out-of-service. DEFAULT: %s]: ' % (parameters.reason))
        else:
            tempReason = raw_input('[ Mandatory ] The redirect REASON [unknown, user-busy, no-answer, unavailable, unconditional, out-of-service]: ')
        if tempReason=='':
            tempReason = parameters.reason
        tempReason = tempReason.strip()

    while True:
        if parameters.isStressTest:
            defaultIsStressTest = 'Y'
        else:
            defaultIsStressTest = 'N'
        tempIsStressTest = raw_input('[ Mandatory ] Do you want to do stress test? [%s]: ' % (defaultIsStressTest))
        if tempIsStressTest=='':
            tempIsStressTest = defaultIsStressTest

        tempIsStressTest = tempIsStressTest.strip().upper()
        if tempIsStressTest=='Y':
            tempIsStressTest = True
            break
        elif tempIsStressTest=='N':
            tempIsStressTest = False
            break

    tempChannelCount = 1
    while tempIsStressTest:
        tempChannelCount = raw_input('[ Mandatory ] How many channels? [%d]: ' % (parameters.channelCount))
        if tempChannelCount=='':
            tempChannelCount = str(parameters.channelCount)

        tempChannelCount = tempChannelCount.strip()
        if tempChannelCount.isdigit():
            tempChannelCount = int(tempChannelCount)
            if tempChannelCount<1:
                print 'The min Channel Count is 1, please try again'
                continue
            else:
                break
        else:
            print 'The Channel Count must be a digit, please try again'
            continue

    parameters.destination = tempDestination
    parameters.calledPrefix = tempCalledPrefix
    parameters.calledCount = tempCalledCount
    parameters.called = tempCalled
    parameters.source = tempSource
    parameters.calling = tempCalling

    parameters.redirectCount = tempRedirectCount
    if tempRedirectCount>0:
        parameters.redirect = tempRedirect
        parameters.reason = tempReason

    parameters.isStressTest = tempIsStressTest
    parameters.channelCount = tempChannelCount

    if not os.path.exists(DIR_CONFIG):
        os.makedirs(DIR_CONFIG)
    parameterFile = file(CALL_PARAMETERS_CONFIG_FILE, 'wb')
    pickle.dump(parameters, parameterFile)
    parameterFile.close()

    callParameters = parameters


def getSnoopFilesFromDir(dir):
    """
    [Function]
    get all snoop files from a dir and its sub-dir (sub...sub-dir) with special ext

    [Argument]
    dir: the directory

    [Return]
    return a list includes all snoop files
    """

    tempAbsdir = os.path.abspath(dir)
    tempAllFiles = os.listdir(dir)
    tempSnoopFiles = []
    for f in tempAllFiles:
        tempName = tempAbsdir+'/'+f
        if os.path.isfile(tempName):
            if os.path.splitext(tempName)[1].lower()==SNOOP_FILE_EXT:
                tempSnoopFiles.append(tempName)
        elif os.path.isdir(tempName):
            tempSnoopFiles += getSnoopFilesFromDir(tempName)

    #print tempSnoopFiles
    return tempSnoopFiles


promptBookDict = None
def loadPromptBookDict():
    global promptBookDict

    if not os.path.exists(BOOK_DB_FILE):
        return None
    #else:

    bookDbFile = file(BOOK_DB_FILE, 'rb')
    promptBookDict = pickle.load(bookDbFile)
    bookDbFile.close()


def getPromptContentById(promptId):
    global promptBookDict

    if not promptBookDict:
        return ''
    #else:

    tempPromptId = promptId.lower()
    if promptBookDict.has_key(tempPromptId):
        return promptBookDict[tempPromptId]
    else:
        return ''


def getSnoopFilesFromList(testCaseListFile):
    """
    [Function]
    get all snoop files according to the test case list file

    [Argument]
    testCaseListFile: the test case list file with special ext

    [Return]
    return a list includes all snoop files listed in the test case list file
    """

    try:
        dir = os.path.split(testCaseListFile)[0]
        if dir=='':
            dir = os.path.abspath(testCaseListFile)

        fileobj = file(testCaseListFile, 'r')

        snoopFilesList = []
        while True:
            tempName = fileobj.readline()
            # EOF
            if not tempName:
                break
            # else:

            tempName = tempName.strip()

            if tempName.startswith(ANNOTATION_CHAR) or len(tempName)==0:
                continue

            tempName = dir+'/'+tempName
            if os.path.exists(tempName):
                if os.path.isfile(tempName):
                    tempExtName = os.path.splitext(tempName)[1].lower()
                    if tempExtName==SNOOP_FILE_EXT:
                        snoopFilesList.append(tempName)
                    elif tempExtName==CASE_LIST_FILE_EXT:
                        snoopFilesList += getSnoopFilesFromList(tempName)
                elif os.path.isdir(tempName):
                    snoopFilesList += getSnoopFilesFromDir(tempName)
            else:
                print "'%s' doesn't exist" % (tempName)

        #print snoopFilesList
        return snoopFilesList
    finally:
        fileobj.close()


def getSnoopFiles():
    gotFileDir = True
    try:
        # PARAMETER -f: File, means to enter file or dir
        tempName = sys.argv[sys.argv.index('-f')+1]
    except ValueError:
        tempName = DIR_CASE

    while True:
        if not gotFileDir:
            tempName = raw_input('Enter the snoop-file/directory/case-list-file(.cl): ').strip()

        if not os.path.exists(tempName):
            print "'"+tempName+"' is a invalid file or dir, please try again"
            gotFileDir = False
            continue

        tempName = os.path.abspath(tempName)
        tempAbspathOfDirCase = os.path.abspath(DIR_CASE)
        if not tempName.startswith(tempAbspathOfDirCase):
            print "The file or dir must in '%s', please take another one" % (tempAbspathOfDirCase)
            gotFileDir = False
            continue

        if os.path.isfile(tempName):
            tempExtName = os.path.splitext(tempName)[1].lower()
            # 1. it's a normal snoop file
            if tempExtName==SNOOP_FILE_EXT:
                tempFiles = [tempName]
                break
            elif tempExtName==CASE_LIST_FILE_EXT:
            # 2. it's a test case list file
                tempFiles = getSnoopFilesFromList(tempName)
                if len(tempFiles)<1:
                    print 'There is no snoop file found according to the case list file', tempName
                    gotFileDir = False
                    continue
                else:
                    break
        elif os.path.isdir(tempName):
            # 3. it's a directory
            tempFiles = getSnoopFilesFromDir(tempName)
            if len(tempFiles)<1:
                print 'There is no snoop file in', tempName
                print "Please make sure the snoop file with the ext '%s'" % (SNOOP_FILE_EXT)
                gotFileDir = False
                continue
            else:
                break

        # else:
        print 'Please make sure your enter is snoop file or dir includes snoop file(s) or case list file with ext', CASE_LIST_FILE_EXT
        gotFileDir = False
        continue

    return tempFiles


def checkPythonVersion():
    if sys.version[:3] not in SUPPORT_PYTHON_VERSIONS:
        print """ERROR!
  The python's version of this machine is %d.%d
  But this tool can only run in python version %s
""" % (sys.version_info[0], sys.version_info[1], ' or '.join(SUPPORT_PYTHON_VERSIONS))
        return False
    else:
        return True


def main():
    print 'Voicebird: version %.2f. Author: Anthony Xu (cabernet1976@163.com)' % (VOICEBIRD_VERSION)
    print

    if not checkPythonVersion():
        return

    # PARAMETER -h: Help
    if '-h' in sys.argv:
        print \
"""OPTIONAL PARAMETERS:
    -h
        get help information

    -f [SNOOP_FILE or DIR or CASE_LIST_FILE]
        tell Voicebird to read which snoop file, dir or case list file (.cl). Voicebird will read
        all cases in sub-dir case/ by default without this parameter

    -y
        with this parameter, Voicebird will bypass asking to set up the Call Parameter and use the
        saved Call Parameters in config file

    -nf
        no call flow will be drawed in the screen when function testing. Note: Voicebird will not
        draw call flow when stress testing

    -nd
        no debug information will be write to log file. Voicebird will write log file by default
        without this parameter

    -vf -vp
        print snoop file's content in the screen, please use like that
        'python voicebird.pyc -f case/1.snoop -vf -vp > content.txt'

    -fp
        Force to Parse every case snoop file, without this parameter (default) system will first
        choice to use the cached

    -pai
        P-Asserted-Identity

    -fdn [FROM_DISPLAY_NAME]
        set From's display name of INVITE message

    -cfdn
        Clear From's display name of INVITE message

CALL PARAMETERS:
    1.  If there is no command line parameter -y, Voicebird will display a Command Line UI to ask
        setting the Call Parameters

    2.  The case can use its own call parameters with a xml file

TIPS:
    Exit by Ctrl+C at anytime"""
        return

    try:
        # 1.
        createLogObj()

        # 2.
        tempFiles = getSnoopFiles()
        snoopParser = SnoopParser(tempFiles)
        caseList = snoopParser.getCaseList()

        if '-vf' in sys.argv or '-vp' in sys.argv:
            return
        #else

        # 3.
        getParameters()
        getFuzzyPrompts()
        loadPromptBookDict()

        LOG.writeLog('-- Call Parameters are as below --\n' + str(callParameters))

        if '-y' not in sys.argv:
            yesOrNo = raw_input('All data is ready, run? [Y/N, default Y]: ').strip().upper()
            if yesOrNo=='':
                yesOrNo = 'Y'

            if yesOrNo=='N':
                return

            while yesOrNo!='Y':
                yesOrNo = raw_input('Run? [Y/N, default Y]: ').strip().upper()
                if yesOrNo=='':
                    yesOrNo = 'Y'

                if yesOrNo=='N':
                    return

        # 4.
        distributor = Distributor(caseList)
        distributor.doSelect()
    except KeyboardInterrupt:
        sys.exit(0)


if __name__=='__main__':
    main()
