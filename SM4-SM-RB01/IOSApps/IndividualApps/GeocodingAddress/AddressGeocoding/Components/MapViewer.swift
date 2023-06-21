//
//  MapViewer.swift
//  AddressGeocoding
//
//  Created by Nom4D on 20/03/2023.
//

import SwiftUI
import MapKit

struct MapViewer: View {
    @EnvironmentObject private var geocoderHandler: GeocoderHandler

    @StateObject private var locationManager: LocationManager = LocationManager()

    var mapView: some View {
        Group {
            if geocoderHandler.currentLocation.coordinates != nil {
                Map(coordinateRegion: $locationManager.region, interactionModes: .all, annotationItems: [geocoderHandler.currentLocation]) { location in
                    MapMarker(coordinate: location.coordinates!)
                }
            } else {
                Map(coordinateRegion: $locationManager.region, interactionModes: .all)
            }
        }
    }

    var body: some View {
        mapView
            .onChange(of: geocoderHandler.currentLocation, perform: { _ in
                if geocoderHandler.isDetailed && geocoderHandler.currentLocation.coordinates != nil {
                    locationManager.region = MKCoordinateRegion(
                        center: geocoderHandler.currentLocation.coordinates!,
                        span: MKCoordinateSpan(latitudeDelta: 0.01, longitudeDelta: 0.01)
                    )
                } else if !geocoderHandler.isDetailed && geocoderHandler.currentLocation.coordinates != nil {
                    locationManager.region = MKCoordinateRegion(
                        center: geocoderHandler.currentLocation.coordinates!,
                        span: MKCoordinateSpan(latitudeDelta: 0.5, longitudeDelta: 0.5)
                    )
                }
            })
            .accessibilityIdentifier("MapViewer")
    }
}
