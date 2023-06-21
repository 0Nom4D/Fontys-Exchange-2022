import 'package:geolocator/geolocator.dart';
import 'package:latlong2/latlong.dart' as latlng;

class Competition{
  Competition({
    required this.name,
    required this.value,
    this.locationRestriction,
    this.timeRestriction
  });

  final String name;
  final String value;
  final Future<bool> Function()? locationRestriction;
  final bool Function()? timeRestriction;

  static List<Competition> competitions = [
    Competition(name: 'BEST STADIUM SELFIE', value: 'best_stadium_selfie', locationRestriction: () async {
      bool serviceEnabled = false;
      LocationPermission permission;

      serviceEnabled = await Geolocator.isLocationServiceEnabled();
      if (!serviceEnabled) {
        return false;
      }

      permission = await Geolocator.checkPermission();
      if (permission == LocationPermission.denied) {
        permission = await Geolocator.requestPermission();
        if (permission == LocationPermission.denied) {
          return false;
        }
      }
      Position position = await Geolocator.getCurrentPosition();
      latlng.LatLng stadiumLocation = const latlng.LatLng(51.4420, 5.4674);
      latlng.LatLng userLocation = latlng.LatLng(position.latitude, position.longitude);
      final double distanceInMeters = const latlng.Distance().distance(stadiumLocation, userLocation);
      if (distanceInMeters <= 1000) {
        return true;
      }
      return false;
    }),
    Competition(name: 'BEST JERSEY PORTRAIT', value: 'best_jersey_portrait'),
    Competition(name: 'BEST OMG MOMENTS', value: 'best_omg'),
    Competition(name: 'BEST CLOSE UP SHOT', value: 'best_close_up', timeRestriction: () {
      DateTime today = DateTime.now();
      DateTime dueDate = today.add(const Duration(days: 2));
      return today.compareTo(dueDate) < 0;
    })
  ];
}