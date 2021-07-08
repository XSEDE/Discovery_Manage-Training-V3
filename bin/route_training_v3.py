#!/usr/bin/env python3

# Copy Training resources information from a source (database and spreadsheet) to the destination (warehouse)
import argparse
from collections import Counter
import datetime
from datetime import datetime, date, timezone, tzinfo, timedelta
from hashlib import md5
import decimal
import json
import logging
import logging.handlers
import os
import psycopg2
import pwd
import re
import shutil
import signal
import sys
from urllib.parse import urlparse
from fuzzywuzzy import process
import urllib.request
import csv
import io
import pytz
Central = pytz.timezone('US/Central')
UTC = pytz.timezone('UTC')

import django
django.setup()
from django.forms.models import model_to_dict
from django.utils.dateparse import parse_datetime
from django_markup.markup import formatter
from resource_v3.models import *
from processing_status.process import ProcessingActivity

import elasticsearch_dsl.connections
from elasticsearch import Elasticsearch, RequestsHttpConnection

import pdb

def datetime_localparse(indate):
    try:
        return(parse_datetime(indate))
    except:
        return(indate)

def datetime_standardize(indate):
    # Localize as Central and convert to UTC
    if isinstance(indate, datetime):
        return(Central.localize(indate).astimezone(tz = UTC))
    else:
        return(indate)

# In order to convert from a map to JSON,
# Decimals and Timestamps need to be converted into strings.
class MissingTypeEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, decimal.Decimal):
            return {'__Decimal__': str(obj)}
        #if isinstance(obj, (datetime.date, datetime.datetime)):
        if isinstance(obj, (date, datetime)):
            return {'__String__': obj.timestamp()}
        # Let the base class default method raise the TypeError
        return json.JSONEncoder.default(self, obj)

class Format_Description():
#   Initialize a Description, smart append, and render it in html using django-markup
    def __init__(self, initial=None):
        self.markup_stream = io.StringIO()
        # Docutils settings
        self.markup_settings = {'warning_stream': self.markup_stream }
        if initial is None:
            self.value = None
        else:
            clean_initial = initial.rstrip()
            self.value = clean_initial if len(clean_initial) > 0 else None
    def blank_line(self): # Forced blank line used to start a markup list
        self.value += '\n'
    def append(self, value):
        clean_value = value.rstrip()
        if len(clean_value) > 0:
            if self.value is None:
                self.value = clean_value
            else:
                self.value += '\n{}'.format(clean_value)
    def html(self, ID=None): # If an ID is provided, log it to record what resource had the warnings
        if self.value is None:
            return(None)
        output = formatter(self.value, filter_name='restructuredtext', settings_overrides=self.markup_settings)
        warnings = self.markup_stream.getvalue()
        if warnings:
            logger = logging.getLogger('DaemonLog')
            if ID:
                logger.warning('markup warnings for ID: {}'.format(ID))
            for line in warnings.splitlines():
                logger.warning('markup: {}'.format(line))
        return(output)

class HandleLoad():
    def __init__(self):
        parser = argparse.ArgumentParser(epilog='File SRC|DEST syntax: file:<file path and name')
        parser.add_argument('-s', '--source', action='store', dest='src', \
                            help='Content source {postgresql} (default=postgresql)')
        parser.add_argument('-d', '--destination', action='store', dest='dest', \
                            help='Content destination {analyze or warehouse} (default=analyze)')
        parser.add_argument('--ignore_dates', action='store_true', \
                            help='Ignore dates and force full resource refresh')
        parser.add_argument('-l', '--log', action='store', \
                            help='Logging level override to config (default=warning)')
        parser.add_argument('-c', '--config', action='store', default='./route_training_v3.conf', \
                            help='Configuration file default=./route_training_v3.conf')
        parser.add_argument('--verbose', action='store_true', \
                            help='Verbose output')
        parser.add_argument('--dev', action='store_true', \
                            help='Running in development environment')
        parser.add_argument('--pdb', action='store_true', \
                            help='Run with Python debugger')
        self.args = parser.parse_args()

        if self.args.pdb:
            pdb.set_trace()

        # Load configuration file
        config_path = os.path.abspath(self.args.config)
        try:
            with open(config_path, 'r') as file:
                conf = file.read()
                file.close()
        except IOError as e:
            raise
        try:
            self.config = json.loads(conf)
        except ValueError as e:
            print('Error "{}" parsing config={}'.format(e, config_path))
            sys.exit(1)

        # Initialize the cutoff level for the fuzzy match algoritm for matching provider names.
        self.FUZZY_SCORE_CUTOFF = int(self.config.get('FUZZY_SCORE_CUTOFF', 90))

        # Initialize logging from arguments, or config file, or default to WARNING as last resort
        loglevel_str = (self.args.log or self.config.get('LOG_LEVEL', 'WARNING')).upper()
        loglevel_num = getattr(logging, loglevel_str, None)
        if not isinstance(loglevel_num, int):
            raise ValueError('Invalid log level: {}'.format(loglevel_num))
        self.logger = logging.getLogger('DaemonLog')
        self.logger.setLevel(loglevel_num)
        self.formatter = logging.Formatter(fmt='%(asctime)s.%(msecs)03d %(levelname)s %(message)s', \
                                           datefmt='%Y/%m/%d %H:%M:%S')
        self.handler = logging.handlers.TimedRotatingFileHandler(self.config['LOG_FILE'], when='W6', \
                                                                 backupCount = 999, utc = True)
        self.handler.setFormatter(self.formatter)
        self.logger.addHandler(self.handler)

        # Verify arguments and parse compound arguments
        SOURCE_URL = getattr(self.args, 'src') or self.config.get('SOURCE_URL', None)
        if not SOURCE_URL:
            self.logger.error('Source was not specified')
            sys.exit(1)
        try:
            self.SOURCE_PARSE = urlparse(SOURCE_URL)
        except:
            self.logger.error('Source is missing or invalid')
            sys.exit(1)

        if self.SOURCE_PARSE.scheme not in ['file', 'http', 'https', 'postgresql']:
            self.logger.error('Source not {file, http, https, postgresql}')
            sys.exit(1)
        if not len(self.SOURCE_PARSE.path or '') >= 1:
            self.logger.error('Source is missing a database name')
            sys.exit(1)

        DEST_URL = getattr(self.args, 'dest') or self.config.get('DESTINATION', 'analyze')
        if not DEST_URL:
            self.logger.error('Destination was not specified')
            sys.exit(1)
        try:
            self.DEST_PARSE = urlparse(DEST_URL)
        except:
            self.logger.error('Destination is missing or invalid')
            sys.exit(1)

        if self.DEST_PARSE.scheme not in ['file', 'analyze', 'warehouse']:
            self.logger.error('Destination not {file, analyze, warehouse}')
            sys.exit(1)

        if self.SOURCE_PARSE.scheme in ['file'] and self.DEST_PARSE.scheme in ['file']:
            self.logger.error('Source and Destination can not both be a {file}')
            sys.exit(1)

        # Initialize appliation variables
        self.memory = {}
        self.PROVIDER_URNMAP = self.memory['provider_urnmap'] = {}
        self.Affiliation = 'xsede.org'
        self.URNPrefix = 'urn:ogf:glue2:'
        self.WAREHOUSE_API_PREFIX = 'http://localhost:8000' if self.args.dev else 'https://info.xsede.org/wh1'
        self.WAREHOUSE_API_VERSION = 'v3'
        self.WAREHOUSE_CATALOG = 'ResourceV3'

        # Loading all the Catalog entries for our affiliation
        self.CATALOGS = {}
        for cat in ResourceV3Catalog.objects.filter(Affiliation__exact=self.Affiliation):
            self.CATALOGS[cat.ID] = model_to_dict(cat)

        self.DefaultValidity = timedelta(days = 14)

        # Map stored by Warehouse provider name contains provider URNs.
        self.PROVIDERS = {}

        # Map stored by class title used to merge class information from the spreadsheet
        # and the portal table. Allow case insensitive searches of keys.
        self.COURSEDATA = {}

        # Map portal class information by class_id so class_sessions can find it later.
        self.COURSEINFO = {}

        # Steps are in the conf/route_* configuration file.
        self.STEPS = []
        for stepconf in self.config['STEPS']:
            if not stepconf.get('LOCALTYPE'):
                self.logger.error('Step LOCALTYPE is missing or invalid')
                sys.exit(1)
            if not stepconf.get('CATALOGURN'):
                self.logger.error('Step "{}" CATALOGURN is missing or invalid'.format(stepconf.get('LOCALTYPE')))
                sys.exit(1)
            if stepconf['CATALOGURN'] not in self.CATALOGS:
                self.logger.error('Step "{}" CATALOGURN is not define in Resource Catalogs'.format(stepconf.get('LOCALTYPE')))
                sys.exit(1)
            myCAT = self.CATALOGS[stepconf['CATALOGURN']]
            stepconf['SOURCEURL'] = myCAT['CatalogAPIURL']

            try:
                SRCURL = urlparse(stepconf['SOURCEURL'])
            except:
                self.logger.error('Step SOURCE is missing or invalid')
                sys.exit(1)
            if SRCURL.scheme not in ['sql','sheet']:
                self.logger.error('Source must be one of {sql, sheet}')
                sys.exit(1)
            stepconf['SRCURL'] = SRCURL

            try:
                DSTURL = urlparse(stepconf['DESTINATION'])
            except:
                self.logger.error('Step DESTINATION is missing or invalid')
                sys.exit(1)
            if DSTURL.scheme not in ['function']:
                self.logger.error('Destination must be one of {function}')
                sys.exit(1)
            stepconf['DSTURL'] = DSTURL
            # Merge CATALOG config and STEP config, with latter taking precendence
            self.STEPS.append({**self.CATALOGS[stepconf['CATALOGURN']], **stepconf})

        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)
        self.logger.info('Starting program={} pid={}, uid={}({})'.format(os.path.basename(__file__), os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

    def Connect_Source(self, urlparse):
        [host, port] = urlparse.netloc.split(':')
        port = port or '5432'
        database = urlparse.path.strip('/')
        conn_string = "host='{}' port='{}' dbname='{}' user='{}' password='{}'".format(host, port, database, self.config['SOURCE_DBUSER'], self.config['SOURCE_DBPASS'] )
        # get a connection, if a connect cannot be made an exception will be raised here
        conn = psycopg2.connect(conn_string)
        # conn.cursor will return a cursor object, you can use this cursor to perform queries
        cursor = conn.cursor()
        self.logger.info('Connected to PostgreSQL database {} as {}'.format(database, self.config['SOURCE_DBUSER']))
        return(cursor)

    def Connect_Elastic(self):
        if 'ELASTIC_HOSTS' in self.config:
            self.ESEARCH = elasticsearch_dsl.connections.create_connection( \
                hosts = self.config['ELASTIC_HOSTS'], \
                connection_class = RequestsHttpConnection, \
                timeout = 10)
            ResourceV3Index.init()
        else:
            self.ESEARCH = None

    def Disconnect_Source(self, cursor):
        cursor.close()

    # Check if a string containing a list of commma separated words
    # has at least one word in common with an array of words.
    def common_member(self, a, b):
        a_set = set(str(a).replace(" ","").split(','))
        b_set = set(b)
        if len(a_set.intersection(b_set)) > 0:
            return(True)
        return(False)

    def Read_Sheet(self, cursor, path, localtype):
        webpage = urllib.request.urlopen(path)
        datareader = csv.DictReader(io.TextIOWrapper(webpage))
        row_num = 0
        DATA = {}
        for row_data in datareader:
            row_num = row_num + 1
            GLOBALID = 'urn:ogf:glue2:info.xsede.org:resource:google:XSEDE_Training_Course:{}'.format(row_num)
            row_data.update( {'id' : row_num} )
            DATA[GLOBALID] = row_data

        return({localtype:DATA})

    def CATALOGURN_to_URL(self, id):
        return('{}/resource-api/{}/catalog/id/{}/'.format(self.WAREHOUSE_API_PREFIX, self.WAREHOUSE_API_VERSION, id))

    def format_GLOBALURN(self, *args):
        newargs = list(args)
        newargs[0] = newargs[0].rstrip(':')
        return(':'.join(newargs))

    def Read_SQL(self, cursor, sql, localtype):
        try:
            cursor.execute(sql)
        except psycopg2.Error as e:
            self.logger.error('Failed "{}" with {}: {}'.format(sql, e.pgcode, e.pgerror))
            sys.exit(1)

        COLS = [desc.name for desc in cursor.description]
        DATA = []
        for row in cursor.fetchall():
            DATA.append(dict(zip(COLS, row)))
        return({localtype: DATA})

    #
    # Delete old items (those in 'cur') that weren't updated (those in 'new')
    #
    def Delete_OLD(self, me, cur, new):

        for URN in [id for id in cur if id not in new]:
            # self.logger.info('DEBUG - deleting: {}'.format(URN))
            try:
                ResourceV3Index.get(id = URN).delete()
            except Exception as e:
                self.logger.error('{} deleting Elastic id={}: {}'.format(type(e).__name__, URN, e))
            try:
                ResourceV3Relation.objects.filter(FirstResourceID__exact = URN).delete()
                ResourceV3.objects.get(pk = URN).delete()
                ResourceV3Local.objects.get(pk = URN).delete()
            except Exception as e:
                self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, URN, e))
            else:
                self.logger.info('{} deleted ID={}'.format(me, URN))
                self.STATS.update({me + '.Delete'})
        return()
    #
    # Update relations and delete relations for myURN that weren't just updated (newURNS)
    #
    def Update_REL(self, myURN, newRELATIONS):
        newURNS = []
        for relatedID in newRELATIONS:
            try:
                relationURN = ':'.join([myURN, md5(relatedID.encode('UTF-8')).hexdigest()])
                relation = ResourceV3Relation(
                            ID = relationURN,
                            FirstResourceID = myURN,
                            SecondResourceID = relatedID,
                            RelationType = newRELATIONS[relatedID],
                     )
                relation.save()
            except Exception as e:
                msg = '{} saving Relation ID={}: {}'.format(type(e).__name__, relationURN, e)
                self.logger.error(msg)
                return(False, msg)
            newURNS.append(relationURN)
        try: # Delete myURN relations that weren't just added/updated (newURNS)
            ResourceV3Relation.objects.filter(FirstResourceID__exact = myURN).exclude(ID__in = newURNS).delete()
        except Exception as e:
            self.logger.error('{} deleting Relations for Resource ID={}: {}'.format(type(e).__name__, myURN, e))

    def Warehouse_Spreadsheet_Training_Class(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Live'
        myRESTYPE = 'Training'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)

        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items in database
        new = {}   # New/updated items
        # Get the list of training classes originally from the google spreadsheet stored in the warehouse.
        for item in ResourceV3Local.objects.filter(Affiliation__exact = self.Affiliation).filter(LocalType__exact = contype):
            cur[item.ID] = item

        # Add the list of training classes originally from the Portal DB stored in the warehouse.
        #NOTE: should be getting the LocalType from the configuration file instead of hard coding it.
        for item in ResourceV3Local.objects.filter(Affiliation__exact = self.Affiliation).filter(LocalType__exact = 'XDCDBTraining'):
            cur[item.ID] = item

        # Merge the spreadsheet course information with the portal data already stored in a map by course title.
        for key, item in content[contype].items():

            provider_id = self.Find_Provider(item['center'])

            myGLOBALURN = self.format_GLOBALURN(self.URNPrefix, 'info.xsede.org', 'resource', 'google_spreadsheet', str(item['id']))


            if item['title'].lower() in self.COURSEDATA:
                DATA = self.COURSEDATA[item['title'].lower()]

                # If the training class is used by a training_class_session,
                # Use myGLOBALURN, LocalID from the Portal database for merged data.
                # This assumes it is using the latest training_class record for its title.

                # If the portal class is used by a session keep its GLOBALURN.
                if DATA['class_used'] == False:
                    DATA['ID'] = myGLOBALURN

                # Merge the JSON data.
                DATA['EntityJSON'] += json.dumps(item, cls=MissingTypeEncoder)

            # This course is unique in the Spreadsheet data, store it in COURSEDATA.
            else:
                DATA = {}
                DATA['ID'] = myGLOBALURN
                DATA['EntityJSON'] = json.dumps(item, cls=MissingTypeEncoder)

            # All unique spreadsheet course data will be stored in the warehouse.
            DATA['store_to_warehouse'] = True

            DATA['LocalID'] = item['id']
            DATA['LocalType'] = contype
            DATA['Name'] = item['title']
            DATA['ShortDescription'] = item['title'] + ", Length: " + item['length']

            # DATA['Description'] = item['description']
            Description = Format_Description(item['description'])

            if item['url'] != None:
                Description.blank_line()
                Description.append('Related resources:')
                Description.blank_line()
                Description.append('- Training URL: {}'.format(item['url']))

            if provider_id == None:
                Description.blank_line()
                Description.append('- Provider: {}'.format(item['center']))

            Description.blank_line()
            Description.append('XSEDE Training Information: https://www.xsede.org/for-users/training')

            DATA['Description'] = Description.html()

            DATA['Topics'] = item['category']
            DATA['Keywords'] = item['level'] + ", " + item['subcategory']

            DATA['ProviderID'] = provider_id

            # Determine if the course is live, streamed, or both.
            event_live = self.common_member(item['delivery'].lower(), ('in-person', 'multicast', 'webinar'))
            event_streamed = self.common_member(item['delivery'].lower(), ('online', 'training portal', 'youtube'))

           # If the delivery has both live and streamed values store 2 separate records for the course.
            course_title = item['title']
            if event_live and event_streamed:
                # Store the course information for the live portion of the course.
                live_course_title = course_title + " - Live"
                DATA['ResourceGroup'] = 'Live Events'
                self.COURSEDATA[live_course_title.lower()] = DATA

                # Set up the course information for the streamed portion of the course to be saved below.
                course_title += " - Streamed"
                DATA['ResourceGroup'] = 'Streamed Events'

            elif event_live:
                DATA['ResourceGroup'] = 'Live Events'
            else:
                DATA['ResourceGroup'] = 'Streamed Events'

            self.COURSEDATA[course_title.lower()] = DATA

        # Store the merged list of spreadsheet and portal classes in the warehouse.
        for course_name, DATA in self.COURSEDATA.items():

            if DATA['store_to_warehouse'] == False:
                continue

            try:
                local = ResourceV3Local(
                            ID = DATA['ID'],
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = DATA['LocalID'],
                            LocalType = DATA['LocalType'],
                            LocalURL = config.get('SOURCEDEFAULTURL', None),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            # Store the item's information appended to its parent's JSON information.
                            EntityJSON = DATA['EntityJSON'],
                    )
                local.save()
            except Exception as e:
                msg = '{} saving Training Class local ID={}: {}'.format(type(e).__name__, DATA['ID'], e)
                self.logger.error(msg)
                return(False, msg)

            new[DATA['ID']] = local

            try:
                resource = ResourceV3(
                            ID = DATA['ID'],
                            Affiliation = self.Affiliation,
                            LocalID = DATA['LocalID'],
                            QualityLevel = 'Production',
                            Name = DATA['Name'],
                            ResourceGroup = DATA['ResourceGroup'],
                            Type = myRESTYPE,
                            ShortDescription = DATA['ShortDescription'],
                            ProviderID = DATA['ProviderID'],
                            Description = DATA['Description'],
                            Topics = DATA['Topics'],
                            Keywords = DATA['Keywords'],
                            Audience = self.Affiliation,
                    )
                resource.save()
                if self.ESEARCH:
                    resource.indexing()
            except Exception as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, DATA['ID'], e)
                self.logger.error(msg)
                return(False, msg)

            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.log_target(me)
        return(True, '')

    def Warehouse_XDCDB_Training_Class(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Live'
        myRESTYPE = 'Training'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        for item in content[contype]:
            provider_id = self.Find_Provider(item['site_name'])

            id_str = str(item['id'])       # From number
            # myGLOBALURN = self.format_GLOBALURN(self.URNPrefix, 'xsede.org', contype, id_str)
            myGLOBALURN = self.format_GLOBALURN(self.URNPrefix, 'info.xsede.org', 'resource', 'xdcdb_session', str(item['id']))

            # The query for the training_class data orders the records by the creation date so just store
            # each record by its training_name in COURSEDATA as it is found and the most recent duplicate
            # entry for each training_name will end up in COURSEDATA before it is merged with the spreadsheet
            # data.

            if item['training_name'].lower() in self.COURSEDATA:
                DATA = self.COURSEDATA[item['training_name'].lower()]

            # Create the new record
            else:
                DATA = {}

            # If the category_id is None then this course is not displayed on the "Portal-Online Training"
            # page. It needs to be found in the query so that its data can be used by a child
            # training_class_session but it should not be written to the warehouse.
            if (item['category_id'] == None):
                DATA['store_to_warehouse'] = False
            else:
                DATA['store_to_warehouse'] = True
            
            DATA['ID'] = myGLOBALURN
            DATA['LocalID'] = id_str
            DATA['LocalType'] = contype
            DATA['EntityJSON'] = json.dumps(item, cls=MissingTypeEncoder)
            DATA['Name'] = item['training_name']

            if item['training_type'] == 'IN_PERSON':
                DATA['ResourceGroup'] = 'Live Event'
            elif item['training_type'] == 'ONLINE_TRAINING' or item['training_type'] == 'WEBCAST':
                DATA['ResourceGroup'] = 'Streamed Events'
            elif item['training_url'] != None:
                DATA['ResourceGroup'] = 'Streamed Events'
            else:
                self.logger.info('{} ResourceGroup set to None'.format(DATA['ID']))
                DATA['ResourceGroup'] = 'None'

            DATA['ShortDescription'] = None
            DATA['Topics'] = None
            DATA['Keywords'] = None
            DATA['class_used'] = False

            if item['training_summary'] == None or item['training_summary'] == '':
                Description = Format_Description(item['training_name'])
            else:
                Description = Format_Description(item['training_summary'])

            if item['contact_email'] != None:
                Description.blank_line()
                Description.append('- Contact email: {}'.format(item['contact_email']))

            if item['training_url'] != None:
                Description.blank_line()
                Description.append('Related resources:')
                Description.blank_line()
                Description.append('- Training URL: {}'.format(item['training_url']))

            if provider_id == None:
                Description.blank_line()
                Description.append('- Provider: {}'.format(item['site_name']))

            Description.blank_line()
            Description.append('XSEDE Training Information: https://www.xsede.org/for-users/training')

            DATA['Description'] = Description.html()

            # Save the course information so it can be looked up later by the training class session.
            course_info = {}
            course_info['Name'] = item['training_name']
            course_info['Description'] = DATA['Description']
            course_info['ResourceGroup'] = DATA['ResourceGroup']
            course_info['Topics'] = DATA['Topics']
            course_info['Keywords'] = DATA['Keywords']
            course_info['EntityJSON'] = DATA['EntityJSON']
            self.COURSEINFO[item['id']] = course_info

            DATA['ProviderID'] = provider_id
            self.COURSEDATA[item['training_name'].lower()] = DATA

        return(True, '')

    def Warehouse_XDCDB_Training_Class_Session(self, content, contype, config):
        start_utc = datetime.now(timezone.utc)
        myRESGROUP = 'Live'
        myRESTYPE = 'Training Session'
        me = '{} to {}({}:{})'.format(sys._getframe().f_code.co_name, self.WAREHOUSE_CATALOG, myRESGROUP, myRESTYPE)
        self.PROCESSING_SECONDS[me] = getattr(self.PROCESSING_SECONDS, me, 0)

        cur = {}   # Current items in database
        new = {}   # New/updated items
        for item in ResourceV3Local.objects.filter(Affiliation__exact = self.Affiliation).filter(LocalType__exact = contype):
            cur[item.ID] = item

        for item in content[contype]:
            id_str = str(item['id'])       # From number
            parent_id = item['training_class_id'] # parent class id
            myGLOBALURN = self.format_GLOBALURN(self.URNPrefix, 'xsede.org', 'resource', 'xdcdb_training_class', id_str)

            try:
                local = ResourceV3Local(
                            ID = myGLOBALURN,
                            CreationTime = datetime.now(timezone.utc),
                            Validity = self.DefaultValidity,
                            Affiliation = self.Affiliation,
                            LocalID = id_str,
                            LocalType = contype,
                            LocalURL = config.get('SOURCEDEFAULTURL', None),
                            CatalogMetaURL = self.CATALOGURN_to_URL(config['CATALOGURN']),
                            # Store the item's information appended to its parent's JSON information.
                            EntityJSON = self.COURSEINFO[parent_id]['EntityJSON'] + json.dumps(item, cls=MissingTypeEncoder)
                    )
                local.save()
            except Exception as e:
                msg = '{} saving Training Session local ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)
            new[myGLOBALURN] = local

            # Use the same name for the session as its parent course.
            session_name = self.COURSEINFO[parent_id]['Name']

            try:
                resource = ResourceV3(
                            ID = myGLOBALURN,
                            Affiliation = self.Affiliation,
                            LocalID = id_str,
                            QualityLevel = 'Production',
                            Name = session_name,
                            ResourceGroup = self.COURSEINFO[parent_id]['ResourceGroup'],
                            Type = myRESTYPE,
                            ShortDescription = item['location_name'],
                            ProviderID = None,
                            Description = self.COURSEINFO[parent_id]['Description'],
                            Topics = self.COURSEINFO[parent_id]['Topics'],
                            Keywords = self.COURSEINFO[parent_id]['Keywords'],
                            Audience = self.Affiliation,
                            StartDateTime = item['start_date'],
                            EndDateTime = item['end_date'],
                     )
                resource.save()
                if self.ESEARCH:
                    resource.indexing()
            except Exception as e:
                msg = '{} saving ID={}: {}'.format(type(e).__name__, myGLOBALURN, e)
                self.logger.error(msg)
                return(False, msg)

            # Flag that the associated course is used by this session.
            self.COURSEDATA[session_name.lower()]['class_used'] = True

            # Set the relationship between the training class and the training class session.
            myNEWRELATIONS = {} # The new relations for this item, key=related ID, value=relation type
            parentURN = self.format_GLOBALURN(self.URNPrefix, 'info.xsede.org', 'resource', 'xdcdb_session', str(item['id']))
            myNEWRELATIONS[parentURN] = 'Live Session'
            self.Update_REL(myGLOBALURN, myNEWRELATIONS)

            self.STATS.update({me + '.Update'})

        self.Delete_OLD(me, cur, new)

        self.PROCESSING_SECONDS[me] += (datetime.now(timezone.utc) - start_utc).total_seconds()
        self.log_target(me)
        return(True, '')

    def Read_Providers(self):

        # Store the provider names in lower case
        for record in ResourceV3.objects.filter(Type__exact = 'Provider'):

            provider_name = record.Name.lower()
            if (provider_name in self.PROVIDERS):
                self.logger.info('Duplicate provider name found in the Warehouse: {}'.format(provider_name))
            else:
                self.PROVIDERS[provider_name] = record.ID

    def Find_Provider(self, provider_name):

        provider_id = None

        if (provider_name.lower() in self.PROVIDERS):
            provider_id = self.PROVIDERS[provider_name.lower()]

        # Perform a fuzzy match of the provider name if an exact match isn't found.
        else:
            (match_name, score) = process.extractOne(provider_name.lower(), self.PROVIDERS.keys())

            if (score > self.FUZZY_SCORE_CUTOFF):
                self.logger.info('Using fuzzy match of {} to {} with score {} cutoff {}'.format(provider_name, match_name, score, self.FUZZY_SCORE_CUTOFF))
                provider_id = self.PROVIDERS[match_name]
                
            else:
                self.logger.info('Provider name not found in the Warehouse: {}'.format(provider_name))

        return(provider_id)

    def SaveDaemonLog(self, path):
        # Save daemon log file using timestamp only if it has anything unexpected in it
        try:
            with open(path, 'r') as file:
                lines = file.read()
                if not re.match('^started with pid \d+$', lines) and not re.match('^$', lines):
                    nowstr = datetime.strftime(datetime.now(), '%Y-%m-%d_%H:%M:%S')
                    newpath = '{}.{}'.format(path, nowstr)
                    shutil.move(path, newpath)
                    print('SaveDaemonLog as {}'.format(newpath))
        except Exception as e:
            print('Exception in SaveDaemonLog({})'.format(path))
        return

    def exit_signal(self, signal, frame):
        self.logger.critical('Caught signal={}, exiting...'.format(signal))
        sys.exit(0)

    def run(self):
        while True:
            if self.SOURCE_PARSE.scheme == 'postgresql':
                CURSOR = self.Connect_Source(self.SOURCE_PARSE)
            self.Connect_Elastic()
            self.STATS = Counter()
            self.Read_Providers()
            self.PROCESSING_SECONDS = {}

            for stepconf in self.STEPS:
                start_utc = datetime.now(timezone.utc)
                pa_application = os.path.basename(__file__)
                pa_function = stepconf['DSTURL'].path
                pa_topic = stepconf['LOCALTYPE']
                pa_about = self.Affiliation
                pa_id = '{}:{}:{}:{}->{}'.format(pa_application, pa_function, pa_topic,
                    stepconf['SRCURL'].scheme, stepconf['DSTURL'].scheme)
                pa = ProcessingActivity(pa_application, pa_function, pa_id , pa_topic, pa_about)

                if stepconf['DSTURL'].scheme != 'function':     # This is already checked in __inir__
                    self.logger.error('Destination scheme must be "function"')
                    sys.exit(1)

                # Retrieve from SOURCE
                if stepconf['SRCURL'].scheme == 'sql':
                    content = self.Read_SQL(CURSOR, stepconf['SRCURL'].path, stepconf['LOCALTYPE'])
                elif stepconf['SRCURL'].scheme == 'sheet':
                    path = ""
                    if stepconf['SRCURL'].query != '':
                        path = stepconf['SRCURL'].path + "?" + stepconf['SRCURL'].query
                    else:
                        path = stepconf['SRCURL'].path
                    content = self.Read_Sheet(CURSOR, path, stepconf['LOCALTYPE'])
                else:
                    self.logger.error('Source scheme must be either "sql" or "sheet"')
                    sys.exit(1)

                # Content does not have the expected results
                if stepconf['LOCALTYPE'] not in content:
                    (rc, message) = (False, 'JSON results is missing the \'{}\' element'.format(stepconf['LOCALTYPE']))
                    self.logger.error(message)
                    pa.FinishActivity(rc, message)
                    continue

                (rc, message) = getattr(self, pa_function)(content, stepconf['LOCALTYPE'], stepconf)
                if not rc and message == '':  # No errors
                    message = 'Executed {} in {:.3f}/seconds'.format(pa_function,
                            (datetime.now(timezone.utc) - start_utc).total_seconds())
                pa.FinishActivity(rc, message)

            # Not disconnecting from Elasticsearch
            self.Disconnect_Source(CURSOR)
            break

    def log_target(self, me):
        summary_msg = 'Processed {} in {:.3f}/seconds: {}/updates, {}/deletes, {}/skipped'.format(me,
            self.PROCESSING_SECONDS[me],
            self.STATS[me + '.Update'], self.STATS[me + '.Delete'], self.STATS[me + '.Skip'])
        self.logger.info(summary_msg)

if __name__ == '__main__':
    try:
        router = HandleLoad()
        myrouter = router.run()
    except Exception as e:
        msg = '{} Exception: {}'.format(type(e).__name__, e)
        router.logger.error(msg)
        sys.exit(1)
    else:
        sys.exit(0)
        
