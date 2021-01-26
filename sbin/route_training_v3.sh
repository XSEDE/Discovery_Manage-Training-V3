#!/bin/bash

### BEGIN INIT INFO
# Provides:          route_training_v3
# Required-Start:    $remote_fs $syslog
# Required-Stop:     $remote_fs $syslog
# Default-Start:     2 3 4 5
# Default-Stop:      0 1 6
# Short-Description: Route Training information from a source to a destination
# Description:       Route Training information from a {file, directory, amqp} to a {directory, api}
### END INIT INFO

####### Customizations START #######
APP_NAME=route_training_v3
APP_BASE=/soft/warehouse-apps-1.0/Manage-Training-V3
WAREHOUSE_BASE=/soft/warehouse-1.0
# Override in shell environment
if [ -z "$PYTHON_BASE" ]; then
    PYTHON_BASE=/soft/python/python-3.7.6-base
fi
####### Customizations END #######

####### Everything else should be standard #######
APP_SOURCE=${APP_BASE}/PROD
WAREHOUSE_SOURCE=${WAREHOUSE_BASE}/PROD

APP_LOG=${APP_BASE}/var/${APP_NAME}.daemon.log
if [[ "$1" != --pdb && "$2" != --pdb && "$3" != --pdb && "$4" != --pdb ]]; then
    exec >${APP_LOG} 2>&1
fi

APP_BIN=${APP_SOURCE}/bin/${APP_NAME}.py
APP_OPTS="-l info -c ${APP_BASE}/conf/${APP_NAME}.conf"

PYTHON_BIN=python3
export LD_LIBRARY_PATH=${PYTHON_BASE}/lib
source ${APP_BASE}/python/bin/activate

export PYTHONPATH=${APP_SOURCE}/lib:${WAREHOUSE_SOURCE}/django_xsede_warehouse
export DJANGO_CONF=${APP_BASE}/conf/django_xsede_warehouse.conf
export DJANGO_SETTINGS_MODULE=xsede_warehouse.settings

do_start () {
    echo "Starting ${APP_NAME}:"
    echo "${PYTHON_BIN} ${APP_BIN} $@ ${APP_OPTS}"
    ${PYTHON_BIN} ${APP_BIN} $@ ${APP_OPTS}
    RETVAL=$?
}

case "$1" in
    start)
        do_${1} ${@:2}
        ;;

    *)
        echo "Usage: ${APP_NAME} {start} [<optional_parameters>]"
        exit 1
        ;;

esac
echo rc=$RETVAL
exit $RETVAL
